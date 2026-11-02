# Actual GL rational-point topology: specialization and dependency supplement

Worker 585 constructed `Langlands.Group.GL.AlgebraicPointTopology` using the
actual algebraic GL comparison of Worker 1107 and the affine point-topology
comparisons of Worker 105. This supplement records the exact continuous maps,
their source provenance and two distinct dependency inventories. It supplements
[the actual general-to-GL adapter note](gl-general-specialization.md) and
[the full GL source map](gl-specialization-source-map.md); those historical
inventories are preserved.

The snapshot is Library `3c99509d9f7a41b5f3932da0e3877264b3a70a9e` plus the
unchanged topology pair in candidate `375283aa-1aa4-4895-8c1c-803fe1fb51e4`.
That candidate has machine validation and Reviewer 9060's independent approval
(review `fb9bd7f7-bd2b-4bc5-892d-82fa3403d8aa`), but is not published at this
snapshot. Publication remains required before downstream reliance on its names.
The three prerequisite pairs below are independently accepted and published
at Library `e530d1eb7e66b0d2b988684aaaa90a729bda10e2`, and are present unchanged
in the snapshot Library.

## Actual carriers, topology and comparison maps

The new declarations in this section have prefix
`Langlands.GroupScheme.GeneralLinear`. The assumptions are exactly a
commutative topological ring `R : Type u`, `IsTopologicalRing R`, a natural
rank `N` and, for block comparisons, `B : Langlands.GeneralLinear.BlockShape N`.
There is no positive-rank, field, Hausdorff or local-compactness hypothesis.
Rank zero and its empty block shape are included.

The rational-point carrier is the actual relative scheme morphism type
`Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ (groupScheme (Fin N) (CommRingCat.of R)).X`.
It explicitly receives the named
`Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology` locally.
This topology is induced by the identity-test equivalence from the existing
affine evaluation topology. The matrix target is `Langlands.GeneralLinear N R`
with the existing matrix-unit topology, which records the entries of both
a matrix and its inverse. Dynamic subgroups use the induced subtype topologies;
quotients use the quotient topologies. Consumers must bind that named topology.
No global rational-point topology instance is installed.

| Declarations | Actual comparison |
| --- | --- |
| `rationalPointsHomeomorph`, `rationalPointsHomeomorph_apply` | Compose the identity-test and affine GL homeomorphisms; prove pointwise equality with the existing algebraic `rationalPointsEquiv`. |
| `rationalPointsContinuousMulEquiv`, its `_apply` lemma, `rationalPoints_isTopologicalGroup` | Retain that same algebraic multiplicative map, prove continuity in both directions, and transport the topological-group property for the specified topology. |
| `rationalParabolicContinuousMulEquiv`, `rationalLeviContinuousMulEquiv`, `rationalUnipotentContinuousMulEquiv` | Restrict the same ambient map to the actual dynamic `P(λ_B)`, `Z(λ_B)` and `U(λ_B)` points and the existing matrix parabolic, embedded Levi and unipotent subgroups. |
| `rationalLeviProductContinuousMulEquiv` | Compose the embedded-Levi comparison with the inverse existing `B.leviEquivContinuous R`, landing in the actual product `B.Levi R`. |
| `rationalLimitContinuousHom`, `rationalLeviProductContinuousMulEquiv_limit` | The underlying homomorphism is literally `Dynamic.limitHom`; its product-Levi image is `B.leviProjection R` of the corresponding matrix. |
| `rationalLeviInclusionContinuousHom`, `rationalParabolicContinuousMulEquiv_inclusion` | The underlying homomorphism is the actual centralizer inclusion into the parabolic; its image is the existing `B.leviAsParabolic R`. |
| `rationalUnipotentContinuousMulEquiv_conj` | Compare the existing dynamic `centralizerConj` with conjugation `z*u*z⁻¹` in the ambient matrix GL group. This is an equality of actual elements. |
| `rationalUnipotentInParabolic`, `_normal`, `rationalLimitContinuousHom_ker` | The quotient denominator is literally the dynamic unipotent subgroup regarded inside the dynamic parabolic. It equals the actual limit kernel. |
| `rationalParabolicQuotientLeviContinuousMulEquiv`, `_mk`, `_symm_apply` | The actual quotient maps `[g]` to the dynamic limit; the inverse maps `z` to the class of its actual inclusion. |
| `rationalParabolicQuotientProductLeviContinuousMulEquiv`, `_mk` | The actual quotient maps to the product Levi by the existing block projection after matrix comparison. |
| `rationalParabolicQuotientMatrixContinuousMulEquiv`, `_mk` | Continuously identify the actual dynamic quotient with `B.parabolic R ⧸ B.unipotentRadical R`; send `[g]` to the class of the corresponding matrix. |

The ambient map equality uses preservation of the underlying scheme morphism
by the identity-test transport and the existing corepresented affine-sections
comparison through `Scheme.ΓSpecIso`. This identifies coordinate maps before
continuity is transferred. Subgroup continuity is restriction of the ambient
map. The limit formula supplies continuity of the existing dynamic limit, and
its actual inclusion section, kernel and the first isomorphism theorem give
the quotient equivalence. The quotient-map criterion and the continuous
inclusion prove continuity in the two directions. These are constructions and
map identities, rather than an assumed comparison package.

## Provenance, prerequisites and frozen bytes

This topology bridge is an internal compatibility construction and asserts no
new literature theorem. Its precise imported provenance is preserved in the
following paired documentation.

| Imported pair and owner | Exact provenance and verified publication |
| --- | --- |
| [Dynamic/GeneralLinearRationalPoints](../../Langlands/GroupScheme/Dynamic/GeneralLinearRationalPoints.md), Worker 1107 | Algebraic rational-point transport of the existing dynamic block-subgroup and limit results; the pair cites CGP, Example 2.1.1, through those existing constructions. Candidate `4ed8ff46-6de0-4f1d-96aa-19069311455b`, integration `cb09c5386b3547d4a0eda7693b3b6570`. |
| [PointTopology/GeneralLinear](../../Langlands/AlgebraicGeometry/PointTopology/GeneralLinear.md), Worker 105 | Derived GL specialization of the existing affine evaluation topology; its paired provenance cites Conrad, Proposition 2.1 and the unit-topology convention. Candidate `cf2810b3-b2ff-40a7-8829-b464b516e77b`, integration `4b188f2848b049d7876198153e9ba4c3`. |
| [PointTopology/RationalPoints](../../Langlands/AlgebraicGeometry/PointTopology/RationalPoints.md), Worker 105 | Derived identity-test transport of that existing topology, preserving the underlying scheme morphisms. Candidate `5ea5f6f1-b141-4215-b595-9b3b6e2c4f8b`, integration `fe55b4013baf4ffebd7f2a294c2b12ae`. |

Native byte comparisons checked both files of each prerequisite against its
accepted archive, the workspace and the snapshot Library. The topology pair
was checked against its own frozen staged copy. The following are source
fingerprints, not independent proof receipts.

| Module | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- |
| `Langlands.AlgebraicGeometry.PointTopology.GeneralLinear` | `3f05f00348cba7b42a5e4141751532aa329572c3d194d4f3c54ac8ea052fccf6` | `5af402a202db4c760b59d356025fc35f75f17d14e3c40b5059b7a9cb1b7ef833` |
| `Langlands.AlgebraicGeometry.PointTopology.RationalPoints` | `b7d672e7ee70d0d16e6b17d69ca3883c296eb69a2207d2978156db84aefdad0d` | `7c0434b9376e9d09db43427b2d73294cabfca86a531f42ec9eba4246592cff5a` |
| `Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints` | `a33fd3082331a9442544442fdcb9c673ba2030f0e7822e7b77461acac5c9c720` | `6e0db00f67c8661891ef7809b469df77c372e8aab359390677f7049f58895fb2` |
| `Langlands.Group.GL.AlgebraicPointTopology` | `448f27e7588e550afb83832264eece4552368991263c4c481049d7cc89599f4d` | `1a104c5f178fd593628c090b69100401d83936c377530c20ad3ad3648509d4cc` |

## Separate declaration and source-import inventories

The private diagnostic `e65d9718-ce02-40ec-ad78-203ffa41d0d9` compiles the
24-root audit with zero errors and warnings at the snapshot. Its program
`.private/drafts/gl-algebraic-point-dependency-audit/GlAlgebraicPointDependencyAudit.lean`
follows each root's checked type, definition/theorem/opaque body and inductive
constructors, including private helpers. It traverses project constants and
prunes nonproject constants; the pinned nonproject modules cannot import
project code. All 24 parsed records equal the earlier diagnostic inventory.

The body/type union contains **26 defining project modules**, with no reached
`Langlands.Representation.Classification` constant. Of its nonempty paired
sources, 25 match the snapshot Library; the additional pair is the topology
bridge. The normalized paired digest is
`02ea6703989ebeb476ee68b931c03c4302f06c671b77e364d0d26027405a6958`.
The exact roots and their individual project-declaration/module counts follow;
all names have prefix `Langlands.GroupScheme.GeneralLinear`, and every root's
Classification-origin constant count is zero.

| Root suffix | Project declarations | Defining project modules |
| --- | ---: | ---: |
| `rationalPointsHomeomorph` | 124 | 11 |
| `rationalPointsHomeomorph_apply` | 155 | 14 |
| `rationalPointsContinuousMulEquiv` | 158 | 14 |
| `rationalPointsContinuousMulEquiv_apply` | 159 | 14 |
| `rationalPoints_isTopologicalGroup` | 159 | 14 |
| `rationalParabolicContinuousMulEquiv` | 376 | 21 |
| `rationalLeviContinuousMulEquiv` | 369 | 21 |
| `rationalUnipotentContinuousMulEquiv` | 465 | 21 |
| `rationalLeviProductContinuousMulEquiv` | 402 | 21 |
| `rationalLimitContinuousHom` | 582 | 24 |
| `rationalLeviProductContinuousMulEquiv_limit` | 584 | 24 |
| `rationalLeviInclusionContinuousHom` | 208 | 14 |
| `rationalParabolicContinuousMulEquiv_inclusion` | 467 | 21 |
| `rationalUnipotentContinuousMulEquiv_conj` | 519 | 23 |
| `rationalUnipotentInParabolic` | 170 | 10 |
| `rationalUnipotentInParabolic_normal` | 183 | 11 |
| `rationalLimitContinuousHom_ker` | 597 | 24 |
| `rationalParabolicQuotientLeviContinuousMulEquiv` | 614 | 24 |
| `rationalParabolicQuotientLeviContinuousMulEquiv_mk` | 615 | 24 |
| `rationalParabolicQuotientLeviContinuousMulEquiv_symm_apply` | 615 | 24 |
| `rationalParabolicQuotientProductLeviContinuousMulEquiv` | 616 | 24 |
| `rationalParabolicQuotientProductLeviContinuousMulEquiv_mk` | 618 | 24 |
| `rationalParabolicQuotientMatrixContinuousMulEquiv` | 628 | 26 |
| `rationalParabolicQuotientMatrixContinuousMulEquiv_mk` | 631 | 26 |

The complete defining-module union is:

- `Langlands.AbelianScheme.GroupScheme`
- `Langlands.AlgebraicGeometry.PointTopology.Affine`
- `Langlands.AlgebraicGeometry.PointTopology.AffineScheme`
- `Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps`
- `Langlands.AlgebraicGeometry.PointTopology.GeneralLinear`
- `Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints`
- `Langlands.AlgebraicGeometry.PointTopology.RationalPoints`
- `Langlands.Group.GL.AlgebraicPointTopology`
- `Langlands.Group.GL.Basic`
- `Langlands.Group.GL.Blocks`
- `Langlands.Group.GL.ParabolicQuotient`
- `Langlands.Group.GL.ParabolicQuotientTopology`
- `Langlands.GroupScheme.Corepresented`
- `Langlands.GroupScheme.CorepresentedAffineComparison`
- `Langlands.GroupScheme.CorepresentedPoints`
- `Langlands.GroupScheme.Dynamic.Basic`
- `Langlands.GroupScheme.Dynamic.Decomposition`
- `Langlands.GroupScheme.Dynamic.GeneralLinear`
- `Langlands.GroupScheme.Dynamic.GeneralLinearOrbit`
- `Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints`
- `Langlands.GroupScheme.Dynamic.LimitMap`
- `Langlands.GroupScheme.Dynamic.Uniqueness`
- `Langlands.GroupScheme.GeneralLinear`
- `Langlands.GroupScheme.Multiplicative`
- `Langlands.GroupScheme.MultiplicativeLaurent`
- `Langlands.GroupScheme.SubgroupFunctor`

Separately, source-import parsing starts only at
`Langlands.Group.GL.AlgebraicPointTopology`, includes the entry module,
strips nested block and line comments, and follows project import commands.
Nonproject imports are recorded as leaves. The source-import closure contains
**33 project modules**, with no `Langlands.Representation` module. Of its
nonempty paired sources, 32 match the snapshot Library and one is additional.
Its normalized paired digest is
`5bc6ada02cbb7108e11185b5d9a2c71c952dd07ba243730f37f827308eaaf5b7`.
The seven import-only modules are `Kernel`, `KernelBaseChange`, `Multiplication`,
`Tate.Twist`, `Torsion` and `TorsionBaseChange` under `Langlands.AbelianScheme`,
and `Langlands.Group.GL.OppositeBlocks`.

The reproducible native script is
`.private/notes/gl_algebraic_point_source_audit.py`. It resolves workspace
sources first, then the named snapshot Library, and preserves the previous
inventories. Full source resolutions, graph edges, paired fingerprints and
frozen comparisons are in
`.private/notes/gl-algebraic-point-source-hashes-3c99509d.json`; all per-root
records are in `.private/notes/gl-algebraic-point-dependencies-3c99509d.json`.
A normalized digest sorts module names and hashes UTF-8 lines
`module<TAB>Lean-SHA256<TAB>Markdown-SHA256<LF>`, including the final newline.

These are two scoped dependency measurements. They neither audit every
declaration in each imported module nor establish classification independence
of the general adapter or the whole Aubert program. They do not replace a
full environment axiom audit. The earlier specialization and graded inventories
retain their representation-theoretic dependencies.

## Remaining assembly and proof obligations

The topology bridge fills the continuous actual-group, dynamic-subgroup,
limit, inclusion, conjugation and quotient comparison described above. It
uses every commutative topological ring; the representation-level exact-K0
adapter continues to retain its existing `PadicField`, complex-coefficient
and saturated-carrier scope. It does not extend representation preservation
to other local-field models.

The independently approved general-to-GL pair
`Langlands.Representation.Aubert.GeneralLinearSpecialization`, candidate
`24537fb1-47eb-4ae1-b7a9-6c0806f21a6d`, is still nonpublic at the snapshot.
Its General prerequisite `214d3c61-c6e3-4576-b94e-57c72d2e7e55` was rejected
for an unqualified BZ77 identification in `General/Parabolic.md`; no replacement
was present in the owner task at this snapshot. A corrected independently
reviewed General prerequisite and reconciliation of its exact bytes are
required before that adapter integrates. Approval of the adapter does not
approve the rejected prerequisite or future replacement bytes.

The adapter's named `Langlands.Parabolic.GeneralLinearModulusCompatibility`
still asks for equality of the Haar-to-block character on the **entire actual
parabolic**, retaining the positive induction half and inverse Jacquet half.
The present topology equivalences do not prove that identity. Actual standard
root/subset, character and Weyl comparisons also retain their owners and
existing targets. The finite external boundary remains the
[Chapter V structural ledger](../renard/chapter-v-structural-inputs.md);
intermediate representation-theoretic premises and its D07 modulus deduction
remain proof work. For support adjustment, product-Levi tensor, monomial
basis and whole graded Zelevinsky targets, use the existing full GL source map.
This focused supplement does not establish those theorems or task completion.
