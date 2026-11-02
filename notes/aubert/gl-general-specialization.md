# Actual general-to-GL Aubert specialization and dependency addendum

Worker 585 constructed the adapter in
`Langlands.Representation.Aubert.GeneralLinearSpecialization` against Worker 23's
shared general interface. This addendum records its actual maps, conditional
scope and exact dependency inventory. It supplements the separately reviewed
[GL source and full-target map](gl-specialization-source-map.md); the older
note's audit snapshot and graded-target inventory remain unchanged.

The present snapshot is Library `0ebc0efd383ff160084af3b33ab2b7806f7a1dde`
with the additional source pairs identified below. The specialization and its
borrowed General dependencies are private development sources, shared for
coordination, rather than published declarations. Their compilation does not
provide independent mathematical acceptance. Status descriptions refer to this
snapshot; consumers must find accepted declarations by Lean name in the current
Library before using them as proof targets.

## Actual construction and retained hypothesis

Fix `B : GeneralLinear.BlockShape n`. The ambient group, upper parabolic,
embedded Levi and radical are the existing `GeneralLinear n F`,
`B.parabolic F`, `B.leviSubgroup F` and `B.unipotentSubgroup F`. The radical is
the ambient image of the kernel of the actual diagonal-block projection.
The product Levi is `B.Levi F`. The existing quotient/product/embedded Levi
comparisons are reused through `Parabolic.LeviModelTransport`.

All abbreviated names in the following table are under `Langlands`.

| Construction | Exact declaration and meaning |
| --- | --- |
| Actual semidirect decomposition | `GeneralLinear.BlockShape.generalSemidirectDecomposition` proves `Aubert.General.IsSemidirectDecomposition` from the existing matrix product and trivial-intersection results. Its projection formula `generalSemidirectDecomposition_projection` is `g ↦ B.leviEquiv F (B.leviProjection F g)`. These algebraic results hold over every commutative ring and in every natural rank. |
| Full modulus target | `GeneralLinear.BlockShape.GeneralModulusCompatibility δ : Prop` equates the actual Haar conjugation modulus on **all of the parabolic** with `δ.comp (B.leviProjection F)`. The target is stronger than an identity only on the Levi. It is an explicit input, not a proved Haar formula. |
| Half conventions | `generalHalfCharacter_eq` identifies the general positive induction half on the entire parabolic. `generalLeviModulus_eq` restricts the full identity to the embedded Levi, and `generalInverseHalfCharacter_eq` identifies the inverse Jacquet half. `blockHalfCharacterOf δ hδ` uses the positive square root of the full character. |
| Full smooth induction | `generalInductionIso` compares general induction after `Parabolic.productToEmbeddedLevi B` with the unchanged block induction. `generalInductionIso_hom_eval` retains every function value. `generalEmbeddedInductionIso` covers every smooth embedded-Levi object after inverse Levi transport, which is needed for preservation on the entire source category. Morphisms retain postcomposition by the original intertwiner. |
| Full smooth Jacquet restriction | `generalJacquetLinearEquiv` uses the existing actual coinvariant quotient equivalences; `generalJacquetLinearEquiv_mk` sends `[v]` to `[v]`. `generalJacquetEquiv` intertwines the normalized actions, and `generalJacquetIso` is natural on the full smooth categories. `generalJacquetIso_hom_mk` gives the formula on every representative. |
| Generic preservation transfer | `generalParabolicFiniteLength_of_block` derives all four general finite-length and short-exact preservation clauses from their block counterparts, through actual Levi pullbacks and the natural isomorphisms above. `Smooth.FiniteLengthGrothendieckIso` supplies isomorphism transport of actual group-algebra length and actual injectivity, surjectivity and range-kernel equality. |
| Actual p-adic specialization | `Parabolic.GeneralLinearModulusCompatibility F T B : Prop` fixes the supplied topology and `δ = T.leviModulus B`. `generalLinearParabolicFiniteLength` derives the four preservation clauses from the existing GL proofs. Only the full modulus target remains a premise of this specialization. |
| Whole exact-K0 maps | With `E = Parabolic.embeddedLeviK0Equiv B`, `generalInductionK0_eq` proves `General.inductionK0 = normalizedInductionK0 ∘ E.symm`; `generalJacquetK0_eq` proves `General.jacquetK0 = E ∘ normalizedJacquetK0`. `generalInductionJacquetK0_eq` cancels the two transports on every class. |
| Actual general operator | `Aubert.generalAlternatingOperator_eq` specializes the existing `General.alternatingOperator` directly along `BlockShape.leviRootSubsetEquiv n`, using the actual subgroup families and derived preservation. It equals the unchanged `Aubert.alternatingOperator F T n` as an integer-linear map. It takes the full modulus hypothesis for every `B : BlockShape n`. |

The smooth comparison assumes a commutative topological ring, `T2Space F`,
local compactness and `NonarchimedeanGroup` for the ambient matrix group, and
an open kernel for the supplied full character. Coefficients are `ℂ`;
the field and representation-carrier universes are independent. Jacquet
retains carrier universe `uV`; induction uses `max uF uV`.

The p-adic part uses the existing `PadicField.{uF} p` and supplied
`T : F.TopologicalData`, including its matrix topology, Hausdorffness, local
compactness and nonarchimedeanness. Its exact-K0 comparison uses the existing
saturated carrier universe `max uF uV`. It does not extend those preservation
proofs to positive-characteristic local fields.

Every map uses the existing exact finite-length Grothendieck group, with
relations from all actual short exact sequences, including nonsplit ones.
These are equalities of entire integer-linear maps. The functor comparisons
are actual natural isomorphisms constructed before passage to K0. No
representation isomorphism is inferred from a virtual-class equality.

The general operator has sign `(-1)^I.card` for a root subset `I`. The existing
root-subset equivalence gives `I.card = n - B.length`. Rank zero is retained:
the unique empty block shape and empty root subset contribute with sign `+1`.
The support adjustment, graded unit, product-Levi tensor comparison, all-segment
monomial comparison and full Theorem 2.3 target remain those of the earlier
GL note. This adapter introduces no second graded ring or replacement operator.

## Source status, evidence and remaining bridges

The own specialization pair is shared in task
`984a6dbb-2caa-4d8d-84c9-b3cd5c4c9cd3`, draft revision 3, content key
`2743f6de0f3a0d9ac4bf66f543d2650ba1bf749fe3003eb1bd3d4c49fde9f762`.
The General pairs were borrowed unchanged from task
`593ef603-6672-4424-976c-14e11e920d9c`, draft revision 1, content key
`190d77087956b751f8481c1c5e6e7af627dfc00b51e35b8708cb145fc4aff697`.
They are not submitted under Worker 585's ownership. That task has no staged
artifact at this snapshot. The exact reviewed dependency is needed before
the focused specialization submission can be finalized.

The generic isomorphism helper is staged as
`6581b7ad-568c-4a4c-bfb4-1780ca65607d`, with machine acceptance and Reviewer
8882's independent approval, awaiting publication. The unchanged Levi-model,
quotient-Jacquet and quotient-induction candidates
`3ffc4cf3-9252-40f6-816b-93b2d24d31ac`,
`d55f4230-35bb-45dd-b63e-196fe462fafe` and
`82b8e447-9f67-4b22-945f-58106eb3ada3` also have machine acceptance and independent
approvals, awaiting publication in that order. Their sources are included in
the audit only where reached or imported.

The latest restoration check is diagnostic
`905b642d-8774-422f-a116-4bc5d4c659da` in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. It reports a successful Lake build with
zero errors and warnings and inspects
`Langlands.Parabolic.GeneralLinearModulusCompatibility` as a definition returning
`Prop`. The reported axioms are `propext`, `Classical.choice` and `Quot.sound`.
This is development evidence for the private overlay, not a publication or
proof receipt.

Worker 1107's algebraic bridge
`4ed8ff46-6de0-4f1d-96aa-19069311455b` has machine acceptance and Reviewer 8833's
independent approval, awaiting publication. Its pair
`GroupScheme.Dynamic.GeneralLinearRationalPoints` constructs
`GroupScheme.GeneralLinear.rationalPointsEquiv`, the actual parabolic, Levi
and radical equivalences, and the projection and section identities
`rationalPointsEquiv_limit`, `rationalLeviEquiv_limitHom` and
`rationalParabolicEquiv_inclusion`. The bridge applies to every commutative
ring and every natural rank, including zero. It is algebraic: it supplies no
homeomorphism or Haar-normalization identity. That pair is not imported by
the present specialization and is not part of either audit closure below.

The remaining comparisons are distinct:

- Identify the actual rational-point topology with the supplied matrix topology,
  compatibly with these subgroup maps. Algebraic equivalences alone do not
  transfer smoothness, Haar measure, or the required topology.
- Prove `Parabolic.GeneralLinearModulusCompatibility` for the supplied topology
  and every block shape. This retains the orientation of the full conjugation
  modulus and therefore both half conventions.
- Reconcile the actual standard subsets, roots, characters and Weyl quotients
  with the shared Chapter V framework, retaining the empty root set and the
  centralizer denominators.
- Publish the reviewed General dependency and the focused own specialization
  pair. Then the parent can use the exact modulus proposition as a focused
  proof target and assemble the general-to-GL comparison.

The [Chapter V ledger](../renard/chapter-v-structural-inputs.md) retains its
itemized external structural boundary. Its D07 Haar/root-product deduction
is not made into an extra external assumption by this conditional adapter.
The existing p-adic representation-theoretic preservation proofs are reused
proved inputs with the dependencies below. The lower whole-ring obligations
listed in the earlier note remain proof obligations for the parent.

## Two separate dependency inventories

The checked-environment audit is diagnostic
`bba8d5fe-f330-437d-87e4-80f48d460e51`. Its private program
`GlGeneralSpecializationDependencyAudit.lean` follows each selected root's
checked type, definition/theorem/opaque body and inductive constructors,
including private proof helpers. It records actual defining modules and prunes
nonproject constants. Nonproject modules cannot import project constants in the
pinned environment. All 17 messages were parsed to the retained file
`.private/notes/gl-general-specialization-dependencies.json`.

The body/type union contains 464 project modules and 67 Classification-origin
constants in ten defining modules. Its 464 nonempty Lean/Markdown pairs were
fingerprinted: 459 match the pinned Library byte for byte, and five are the
additional pairs identified in the tables below. The normalized paired
fingerprint digest is
`2ff834784d0b6a1bc7441689c355e3e6692a77e18fc2daca13939fff3b99befc`.

Separately, native source parsing follows project import commands from the four
entry modules: `GeneralLinearSpecialization`, `Smooth.FiniteLengthGrothendieckIso`,
`General.Parabolic` and `General.AlternatingOperator`, under their full
`Langlands.Representation` prefixes. It strips nested block comments and line
comments, includes each root, follows project imports and lists nonproject
imports as leaves. This source-import union contains 621 project modules,
including fourteen Classification modules. All 621 pairs are nonempty;
613 match the pinned Library byte for byte and eight are additional.
Its normalized paired fingerprint digest is
`34947fc790c5049729ae3173c1da1854aafeb931e7c7150daf1522ce13d240f0`.

The full source resolutions, graph edges and fingerprints for both inventories
are retained in `.private/notes/gl-general-specialization-source-hashes.json`,
generated by `.private/notes/gl_general_source_audit.py`. Resolution priority
is the private overlay, then workspace, then pinned Library. A digest sorts
module names and hashes the UTF-8 lines
`module<TAB>Lean-SHA256<TAB>Markdown-SHA256<LF>`, including the final newline.
The source-import closure contains 157 project modules not reached through the
17 selected bodies/types; it is not substituted for that declaration inventory.

Compared with the earlier 27-root inventory, all 67 Classification-origin
constants were already among its 420. The new body/type module union adds only
`Aubert.General.Parabolic`, `Aubert.General.AlternatingOperator`,
`Aubert.GeneralLinearSpecialization`, `Jacquet.Localization` and
`Smooth.FiniteLengthGrothendieckIso`, under `Langlands.Representation`.
This is a comparison of selected inventories, not an assertion that every
declaration in those modules has been audited.

The generic preservation root reaches only
`FiniteLengthAssembly.length_comp_surjective` and
`finiteLength_comp_surjective_iff`. These prove invariance of module length
through the explicit invariant-subspace order equivalence for a surjective
group homomorphism. Their defining module has Classification in its path;
their use here is algebraic transport.

The p-adic preservation, K0 and operator roots reach the existing normalized
parabolic preservation chain. That chain includes finite-length admissibility,
admissible product-Levi factorization, irreducible product embeddings and length,
normalized induction length, supercuspidal support and twists, and refined
Jacquet length induction. The new natural-isomorphism helper adds no
Classification import. None of these facts certifies semantic independence
of the whole module or unrestricted eligibility for a separate upstream task.

The tables below list every selected root and every Classification-origin
constant, including private helpers. Keys refer only to this addendum.

### Selected body/type roots

| Key | Exact root | Project declarations | Project modules | Classification-origin constants |
| --- | --- | ---: | ---: | ---: |
| G1 | `Langlands.GeneralLinear.BlockShape.generalSemidirectDecomposition` | 75 | 6 | 0 |
| G2 | `Langlands.GeneralLinear.BlockShape.generalSemidirectDecomposition_projection` | 94 | 6 | 0 |
| G3 | `Langlands.GeneralLinear.BlockShape.GeneralModulusCompatibility` | 119 | 7 | 0 |
| G4 | `Langlands.GeneralLinear.BlockShape.generalInductionIso` | 276 | 22 | 0 |
| G5 | `Langlands.GeneralLinear.BlockShape.generalJacquetIso` | 318 | 26 | 0 |
| G6 | `Langlands.GeneralLinear.BlockShape.generalEmbeddedInductionIso` | 275 | 21 | 0 |
| G7 | `Langlands.GeneralLinear.BlockShape.generalParabolicFiniteLength_of_block` | 433 | 37 | 2 |
| G8 | `Langlands.Parabolic.GeneralLinearModulusCompatibility` | 169 | 14 | 0 |
| G9 | `Langlands.Parabolic.generalLinearParabolicFiniteLength` | 5518 | 460 | 67 |
| G10 | `Langlands.Parabolic.generalInductionK0_eq` | 5571 | 461 | 67 |
| G11 | `Langlands.Parabolic.generalJacquetK0_eq` | 5571 | 461 | 67 |
| G12 | `Langlands.Parabolic.generalInductionJacquetK0_eq` | 5577 | 461 | 67 |
| G13 | `Langlands.Aubert.generalAlternatingOperator_eq` | 5634 | 464 | 67 |
| G14 | `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.mapOfIso` | 49 | 6 | 0 |
| G15 | `Langlands.Aubert.General.normalizedInductionFunctor` | 111 | 12 | 0 |
| G16 | `Langlands.Aubert.General.jacquetFunctor` | 123 | 15 | 0 |
| G17 | `Langlands.Aubert.General.alternatingOperator` | 215 | 21 | 0 |

### Source-import roots

Counts include the root module. Names in this table have prefix
`Langlands.Representation.`.

| Root module | Imported project modules | Classification modules |
| --- | ---: | ---: |
| `Aubert.GeneralLinearSpecialization` | 621 | 14 |
| `Smooth.FiniteLengthGrothendieckIso` | 8 | 0 |
| `Aubert.General.Parabolic` | 85 | 5 |
| `Aubert.General.AlternatingOperator` | 294 | 9 |

The four Classification modules imported without a reached constant in this
17-root body/type union are `ConstituentRelations`, `FiniteLengthStatement`,
`Segments` and `SupercuspidalContragredientStatement`, under
`Langlands.Representation.Classification`. Their paired hashes are also given
below. Imported module membership is not use of every declaration it contains.

### Complete Classification-origin constant membership

#### Langlands.Representation.Classification.FiniteLengthProof

| Declaration | Roots |
| --- | --- |
| `Langlands.FiniteLengthAssembly.complementaryProjection` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.complementaryProjection._proof_1` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.complementaryProjection._proof_2` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.complementaryProjection_surjective` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.finiteLength_comp_surjective_iff` | G7, G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.finiteLength_normalizedJacquet_of_refinements` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.finiteLength_of_complement` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.finiteLength_of_complement._simp_1_2` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.finiteLength_of_complement._simp_1_3` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.finiteLength_of_injective` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.finiteLength_of_refinedJacquet` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.finiteLength_of_surjective` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.finite_of_surjective` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.finite_summand` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.isAdmissible_levi_subrepresentation` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.isAdmissible_normalizedJacquet` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.length_comp_surjective` | G7, G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.length_eq_add_of_complement` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.normalizedJacquet_eq_twist` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.refinedJacquetMap_surjective` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.refinement_measure_lt` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteLengthAssembly.refinement_measure_lt._proof_1_1` | G9, G10, G11, G12, G13 |
| `Langlands.Parabolic.normalizedJacquetFiniteLength` | G9, G10, G11, G12, G13 |

#### Langlands.Representation.Classification.IrreducibleProductEmbedding

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.irreducibleProductEmbedding` | G9, G10, G11, G12, G13 |
| `Langlands.Classification.irreducibleProduct_embedding` | G9, G10, G11, G12, G13 |
| `Langlands.Classification.irreducible_supercuspidalProduct_embedding` | G9, G10, G11, G12, G13 |
| `Langlands.Classification.normalizedProduct_embedding_of_factor_embeddings` | G9, G10, G11, G12, G13 |
| `Langlands.FiniteTensor.externalMap_injective` | G9, G10, G11, G12, G13 |

#### Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.IrreducibleProductEmbeddingTheorem` | G9, G10, G11, G12, G13 |

#### Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.irreducibleProductFiniteLength` | G9, G10, G11, G12, G13 |
| `_private.Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof.0.Langlands.Classification.flattenSupercuspidalFactors` | G9, G10, G11, G12, G13 |
| `_private.Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof.0.Langlands.Classification.flattenSupercuspidalFactors_obj` | G9, G10, G11, G12, G13 |

#### Langlands.Representation.Classification.NormalizedProductFiniteLengthProof

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.ProductLengthProof.finiteLength_of_injective` | G9, G10, G11, G12, G13 |
| `Langlands.Classification.ProductLengthProof.finiteLength_of_range_eq_ker` | G9, G10, G11, G12, G13 |
| `Langlands.Classification.ProductLengthProof.finiteLength_of_surjective` | G9, G10, G11, G12, G13 |
| `Langlands.Classification.ProductLengthProof.irreducibleLevi` | G9, G10, G11, G12, G13 |
| `Langlands.Classification.ProductLengthProof.leviPreservation` | G9, G10, G11, G12, G13 |
| `Langlands.Classification.ProductLengthProof.step` | G9, G10, G11, G12, G13 |
| `Langlands.Classification.normalizedInductionFiniteLength` | G9, G10, G11, G12, G13 |

#### Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement

| Declaration | Roots |
| --- | --- |
| `Langlands.Classification.IrreducibleProductFiniteLength` | G9, G10, G11, G12, G13 |

#### Langlands.Representation.Classification.Supercuspidal

| Declaration | Roots |
| --- | --- |
| `Langlands.GeneralLinear.BlockShape.conjugateUnipotent` | G9, G10, G11, G12, G13 |
| `Langlands.GeneralLinear.IsSupercuspidal` | G9, G10, G11, G12, G13 |
| `Langlands.GeneralLinear.SupercuspidalRep` | G9, G10, G11, G12, G13 |
| `Langlands.GeneralLinear.isSupercuspidal_of_equiv` | G9, G10, G11, G12, G13 |
| `Langlands.GeneralLinear.supercuspidalProperty` | G9, G10, G11, G12, G13 |
| `Langlands.Jacquet.coinvariantsEquiv` | G9, G10, G11, G12, G13 |
| `Langlands.Jacquet.coinvariantsEquiv._proof_1` | G9, G10, G11, G12, G13 |
| `Langlands.Jacquet.coinvariantsEquiv._proof_2` | G9, G10, G11, G12, G13 |
| `Langlands.Jacquet.coinvariantsEquiv._proof_3` | G9, G10, G11, G12, G13 |
| `Langlands.Jacquet.coinvariantsEquiv._proof_4` | G9, G10, G11, G12, G13 |
| `Langlands.Jacquet.coinvariants_subsingleton_iff` | G9, G10, G11, G12, G13 |

#### Langlands.Representation.Classification.SupercuspidalContragredientAux

| Declaration | Roots |
| --- | --- |
| `Langlands.GeneralLinear.isSupercuspidal_iff_standard` | G9, G10, G11, G12, G13 |
| `Langlands.Jacquet.coinvariantsConjEquiv` | G9, G10, G11, G12, G13 |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_1` | G9, G10, G11, G12, G13 |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_2` | G9, G10, G11, G12, G13 |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_3` | G9, G10, G11, G12, G13 |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_4` | G9, G10, G11, G12, G13 |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_5` | G9, G10, G11, G12, G13 |
| `Langlands.Jacquet.coinvariantsConjEquiv._proof_6` | G9, G10, G11, G12, G13 |
| `Langlands.Jacquet.coinvariants_conj_subsingleton_iff` | G9, G10, G11, G12, G13 |
| `Langlands.isIrreducible_iff_of_equiv` | G9, G10, G11, G12, G13 |

#### Langlands.Representation.Classification.SupercuspidalSupport

| Declaration | Roots |
| --- | --- |
| `Langlands.SmoothRep.IsSubquotient.of_iso_right` | G9, G10, G11, G12, G13 |
| `Langlands.SmoothRep.hom_hom_injective` | G9, G10, G11, G12, G13 |
| `Langlands.SmoothRep.hom_hom_surjective` | G9, G10, G11, G12, G13 |
| `Langlands.SmoothRep.isSubquotient_iff_exists` | G9, G10, G11, G12, G13 |
| `Langlands.SmoothRep.isSubquotient_iff_exists.match_1_1` | G9, G10, G11, G12, G13 |

#### Langlands.Representation.Classification.SupercuspidalTwist

| Declaration | Roots |
| --- | --- |
| `Langlands.GeneralLinear.BlockShape.determinant_eq_one_of_mem_unipotentSubgroup` | G9, G10, G11, G12, G13 |

### Additional source pairs

All eight pairs occur in the source-import union. The body column says whether
the module also occurs in the selected body/type union. Status is as described
above; none of these eight pairs is present in the pinned Library.

| Module | Body/type union | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Group.GL.ParabolicQuotientTopology` | no | `f92c3ece2b297398ef0781baf7ba336471cd6f6a45077f13ecb9c16e6fe0584c` | `0b4ca5e6ea35193207f7aa74113269da1b8b41815d3d355f4e7a7e96a1ee59d2` |
| `Langlands.Representation.Aubert.General.AlternatingOperator` | yes | `b56f56ea098478823cac01a3b942a1288ea3140d7aff49227e805b84e71db694` | `c0f5f0811bd6da882333992d023a8605b1ead50090a569b8831a388062ce6b38` |
| `Langlands.Representation.Aubert.General.Parabolic` | yes | `f4b1a991bcdfb1dcd36e6b98308099e71dec4d86ffc5680834d44ae833c56d18` | `b173dafedf777b6cd94d53d92cf02b08b5e9f5ab86c1f47b4d5b1fafc5f4d578` |
| `Langlands.Representation.Aubert.GeneralLinearSpecialization` | yes | `b789bdd6dcdf42c82b00d07186587797a5e7b590ee9f47812a3ef6fa04dc3b2c` | `07641006e9a2f8a8d32ed6d3225bb33d39fd930a7b6b9658e1920b5fd98485bd` |
| `Langlands.Representation.Parabolic.LeviModelTransport` | yes | `e28f0cabcbee3c48e0ccdead8af92f5a187dfe6f703d6c1c7a8bf58b032fd004` | `1862a238c7cdc96974df25f0f54e9ed40caafd0a2552a13c8f26a01d0e0781a0` |
| `Langlands.Representation.Parabolic.QuotientInductionComparison` | no | `9140ea542f766a9288ecf3d4e13223bf290670ec6691e69b17d4efc0eb7ac5bc` | `5917ef5080187681656da395c55987be19a5cf60201292d99357d62b70cd5295` |
| `Langlands.Representation.Parabolic.QuotientJacquetComparison` | no | `e7884f2389a72cd066329a15e67ede64f3875f6e49110c6a90980d625896239b` | `874e13a9ed861ca3b1022c19e4aeb6cf669f6283e8b01f295713cdde43339d46` |
| `Langlands.Representation.Smooth.FiniteLengthGrothendieckIso` | yes | `24f9f3ebc44bd56885eac3290d65fef5f4682947e282dd173a0991845a5ed89d` | `5dbb6fc79f8b99a2ab1002c6b82d3b9b573d100b855ae229b133c1af8cc5f68a` |

### Classification module fingerprints

All fourteen source pairs below match the pinned Library exactly. The body
column distinguishes the ten defining modules reached through constants from
the four additional imports. Hashes are source fingerprints, not proof receipts.

| Module suffix under `Langlands.Representation.Classification` | Body/type union | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `ConstituentRelations` | no | `deb56924ecebd5c12a875ecf69f4b4960801e3ed6df5d8fe013c9a303cd58721` | `47047bc2be3ee74e4be6e5077319f06c463d7e446b586f7b3d4b58e016d8641d` |
| `FiniteLengthProof` | yes | `a43bc7e1a097f6441ad180310c1301e5a22166eacc18c325a47d2baf129baaa8` | `2f084b7d91939088137a46eac5d6cfef1ee00473d754bd54bab7bc3030179641` |
| `FiniteLengthStatement` | no | `b35baf903670b558bbc5fbae97d4f8350c21f72553bc844bd7c858fcb64ee46d` | `dc554c0a5dc5352804716353022e8a971cf345ef51bb8c0591dd063d7a27b1fb` |
| `IrreducibleProductEmbedding` | yes | `0a999855052b3dbbaceaed17741d151b354627faf3004049c9ce58232ef00f4e` | `2c581f724e233c558b874480ef5d4c40199dc81a763f8ddd12590787c7330f0a` |
| `IrreducibleProductEmbeddingStatement` | yes | `15aae2c06f59c603bdbb162faad33d14fadaf462bb14429dd374b21492a052d5` | `a6a9843c1f66aa4d2e83595ec35a40315c3a84d8c30d7d0b03924e578831b709` |
| `IrreducibleProductFiniteLengthProof` | yes | `a33e3cec646613d2850af65b070ce61e1bac5f15cb2f27e5a20bf7939286e4c1` | `2dab0bc3ddb209af152cf88ec9a77551618eff1bcb77f6fee8df23e26fc3c0f1` |
| `NormalizedProductFiniteLengthProof` | yes | `6dbdffc815e2d8c4020e68d71e25f1a79d0251edf9512201dc027af1d717072a` | `9609c9d7b5ad6e66247a1727ae2f4edb3f34f76bcd4e14120379fa2bd4db7c60` |
| `NormalizedProductFiniteLengthStatement` | yes | `ad77de724ec74c75a6fd349b61119f6fa106adef2bf204f28d26c87c70ccf6b5` | `e428d95b452fadae47625d55cdd3b3ce89fc44292547de8f57c3631e982830d5` |
| `Segments` | no | `b09e9fdc1445e6fabe2a923a896c5f0f5675fe31fd0f8adc7fe351e98346edda` | `ba5682b3f3e143817d63133383fc3b05469cc48f05ed20c9aaee5344b272189f` |
| `Supercuspidal` | yes | `c13ba8ffad11de2c3b2861c4afc385be2663b3e76963d5e89807ba92c753f9f1` | `b46be626d8b287d7011f47c8ee66cc8e22620efb6a94c0086486d75ee212f09d` |
| `SupercuspidalContragredientAux` | yes | `b073fcfb57858c9a80029ebb148aabf16597a953d75c04dfd8967652908e3713` | `4a75bb9194c2ae7d0bbb31a1cc2b1e1668b9ea28ea953faa683d361bc979ae29` |
| `SupercuspidalContragredientStatement` | no | `d56c904f48439794e34a4029152063a94a19a2bfa908f15102eeb023e7971177` | `3904bee0caf97f7b1b558369b985149ed3378d57fb362b99837ca966c0b6de2b` |
| `SupercuspidalSupport` | yes | `4680302c6b5ad320893b38e1787f11739aca615cc8f44b38021824423089990a` | `7f8064dc6500a598053a8dcbf6dfba8fdc1a6413b49ccb4cabc3267eae4e6e1f` |
| `SupercuspidalTwist` | yes | `057738fc8e7b1aeaee62186dec29b412049a22f15ac7f71ff7759eaea1bf2b58` | `f3ed69bf8418af1014b430c58193a8bce4797cd18e72673207d7f0164d695fa6` |
