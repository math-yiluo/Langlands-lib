# Absolute structure: family 4 coverage update

Worker 3483, 13 November 2026, for Task 3483
(`2b5e4a00-9d44-49a4-9c89-979fb5b6233e`).

At Library commit `aad41a6eb68efecf631ccac31f2e33766f3711f1`, four
entries listed as composites in the
[family 4 ledger](ledger-family-4-absolute.md) have exact named proof
theorems: C13, E3 and the first two internal interfaces of F. This update
marks those entries P under the ledger's convention: a theorem in the
published Library has exactly the named statement as its type. The
[21 November update](#verified-proof-publications-21-november-2026) records
the later publications for C11 and the third interface of F.

All declaration names below have prefix `Langlands.GroupScheme`; module
paths have prefix `Langlands/GroupScheme/`.

| Ledger entry | Exact statement | Published theorem | Proof module |
| --- | --- | --- | --- |
| C13 | `PseudoReductiveCentralCocharacterStatement` | `pseudoReductiveCentralCocharacter` | `Dynamic/PseudoReductiveCentralCocharacterProof` |
| E3 | `Dynamic.LeviAdjointDeterminantReciprocityStatement` | `Dynamic.leviAdjointDeterminantReciprocity` | `Dynamic/LeviAdjointDeterminantReciprocityProof` |
| F, first interface | `AbsoluteBorelOvergroupRootInversionStatement` | `absoluteBorelOvergroupRootInversion` | `Absolute/BorelOvergroupRootInversionProof` |
| F, second interface | `AbsoluteBorelOvergroupRankOneContainmentStatement` | `absoluteBorelOvergroupRankOneContainment` | `Absolute/BorelOvergroupRankOneContainmentProof` |

Each theorem has the displayed statement as its type at every universe
`u`, with no additional premises outside the statement.

## C13: full dynamic parabolics in pseudo-reductive groups

The [statement](../../Langlands/GroupScheme/Dynamic/PseudoReductiveCentralCocharacterStatement.md)
quantifies over every field, actual pseudo-reductive group scheme `G`
and cocharacter `χ`. It proves
`Dynamic.parabolic χ = ⊤ ↔ Dynamic.centralizer χ = ⊤`.
Pseudo-reductivity here uses the ground-field unipotent radical; no
perfectness, splitting or geometric reductivity hypothesis is added.
Both equalities are equalities of subgroup functors on every scheme test,
including nonreduced tests.

The [proof](../../Langlands/GroupScheme/Dynamic/PseudoReductiveCentralCocharacterProof.md)
uses the affine representative `Dynamic.Affine.unipotentHom χ`,
its closedness and representability, and `dynamicUnipotentUnipotence`.
It then applies
`Dynamic.parabolic_eq_top_iff_centralizer_eq_top_of_isUnipotent`
with the trivial ground-field unipotent radical supplied by
`IsPseudoReductive G`.
The inherited source is CGP, Lemma 2.2.3(2), printed pp.62–63 /
PDF pp.88–89. This theorem supplies no relative-root reflection or
normalizing representative.

## E3: opposite determinant characters on a common dynamic Levi

The [statement](../../Langlands/GroupScheme/Dynamic/LeviAdjointDeterminantReciprocityStatement.md)
retains every field and every actual connected reductive group. Its
cocharacter is a cocharacter of a specified maximal split torus followed
by its inclusion into `G`. The represented models of both opposite
unipotent subgroups, their finite Lie coordinates, and a common affine
model of the two equal centralizers are arbitrary, subject to the
displayed representability and affineness premises.

The two determinant characters add to zero in the additive character
group of that common centralizer. On points their values therefore
multiply to one. This is an algebraic character identity; it asserts no
Haar-measure comparison. This particular target retains its restriction
to cocharacters of the specified maximal split torus.

The [proof](../../Langlands/GroupScheme/Dynamic/LeviAdjointDeterminantReciprocityProof.md)
applies `leviAdjointDeterminantReciprocity_of_structure` to the
published proofs `relativeRootReflectionExistence`,
`centralSplitTorusCharacter` and `dynamicCentralizerReductive`.
There are no remaining theorem premises in this application.
The statement's Markdown explains its derived provenance from CGP,
Lemma 2.1.5 and Proposition 2.1.8(1), and the separate motivation from
Renard V.5.4. The character identity is not presented as a verbatim
assertion of those sources.

## F: the two overgroup interfaces

Both statements use an actual split maximal torus `j : T ⟶ G`,
a smooth connected closed subgroup `i : P ⟶ G`, and an actual lift
`t : T ⟶ P` with `t ≫ i = j`. The ambient group is connected reductive.
The premises require both signs of a root `α` in the intrinsic
tangent-weight support of `P`.

The [first interface](../../Langlands/GroupScheme/Absolute/BorelOvergroupRootInversion.md)
is over algebraically closed fields. Its
[named proof](../../Langlands/GroupScheme/Absolute/BorelOvergroupRootInversionProof.md)
introduces the statement's hypotheses and applies
`AbsoluteBorelOvergroup.exists_supportPreserving_weylInverter_of_both_signs`.
It supplies an element of the actual `relativeWeylGroup j` sending
`α` to `−α` and preserving the entire displayed tangent-weight support.
It asserts neither a coroot nor a reflection formula on other characters.

The [second interface](../../Langlands/GroupScheme/Absolute/BorelOvergroupRankOne.md)
works over every field. Its
[named proof](../../Langlands/GroupScheme/Absolute/BorelOvergroupRankOneContainmentProof.md)
applies
`AbsoluteBorelOvergroup.rankOneCentralizer_le_range_of_both_signs`.
Its conclusion is containment of the dynamic centralizer of the specified
rank-one cocharacter in `SubgroupFunctor.range i`, on every test scheme.

These are internal interfaces derived from the published rank-one,
Lie-weight and centralizer constructions. Smoothness and connectedness of
`P` remain explicit premises. These two theorems alone do not construct
the cocharacter of a general Borel overgroup. No duplicate wrapper tasks
are needed.

## Proof status on 13 November 2026

**C11, supplied dynamic quotient properness.** The current owner is
Task 6453, `5934d030-06ab-45a5-bed4-6bd68943c20d`, revision 1, for
`DynamicQuotientProperStatement`. The historical Task 4665 identifier
in the ledger is unavailable after restoration; exact and broader task
searches preceded publication of this successor.

The unchanged [target](../../Langlands/GroupScheme/Dynamic/QuotientProperStatement.md)
retains every algebraically closed field, every cocharacter including
trivial and central ones, and the same supplied relative scheme `Q` and
map `q`. The structure map of `Q` is separated, locally of finite type
and quasi-compact; `q` is smooth, surjective and quasi-compact.
The right-coset fiber equality holds on every relative scheme test.
The conclusion is properness of that particular `Q`.

Task 6453 retains the independent-route restriction documented in the
[source map](dynamic-quotient-source-map.md). It excludes the
regular-cocharacter/Borel route, parabolic-dynamic classification,
rank-one solvable obstruction, rank-one Borel-dynamic theorem,
rank-one positive-root uniqueness, and results proved downstream from
those inputs. Their present publication does not waive the restriction.
The ledger's composite through `parabolicDynamic` therefore does not
discharge this obligation. No full independent proof draft was supplied.

**F, third interface, triangular diagonal kernel tower.** Task 6428,
`70f1e978-f31e-4051-a9cb-8cff40e69c8a`, revision 1, owns the exact
`TriangularDiagonalKernelTowerStatement`. The
[target](../../Langlands/GroupScheme/Absolute/TriangularDiagonalKernelTowerStatement.md)
retains every field, the supplied closed triangular inclusion and its
actual fppf diagonal quotient `q : H ⟶ D(Λ)`, with finitely generated
possibly torsion `Λ`. It requires a finite character-linear tower for
this very `q`, with actual quotient kernels and an isomorphism as the
terminal structural map. No smoothness, connectedness or reducedness
premise is added; no section is asserted.

A complete unreviewed proof pair is shared as that task's draft revision 1.
It applies
`TriangularLayer.admitsTower_diagonalizable_of_affine_image_and_normal_quotient`
to the published proofs `affineHomImage` and
`affineNormalSubgroupQuotient`. The draft compiles with zero errors and
warnings and uses only `propext`, `Classical.choice` and `Quot.sound`.
Thus this entry can now be classified C rather than O. Exact-target
validation, independent semantic acceptance and proof publication remain
outstanding. At the task inspections for this update, both proof tasks
were ready, with no executor or submitted artifact.

## Verification and retained limits

Worker 3483 reread the complete Lean and Markdown pairs for all four
statements and proofs in the table. All sixteen files match the stated
Library commit byte for byte. A development Lake check rebuilt the four
proof modules with zero errors and warnings; inspection of
`absoluteBorelOvergroupRankOneContainment` reported only `propext`,
`Classical.choice` and `Quot.sound`. Development checks verify this
reconciliation and provide no new independent proof acceptance.

The theorem/module pairs in the table are the published mathematical
evidence. The source locators above are inherited from their paired
Markdown; this update introduces no new source assertion or Lean result.
The five components of C12 remain available by projection from the
published `GeneralLinear.dynamicStatement` conjunction, as recorded in
the ledger; no separate wrapper task is needed.

The ledger's other scope differences remain: A6 gives a point form of the
normalizer theorem, A10 does not assert `P = N_G(P)`, A11 gives the
existence half, B7 is over algebraically closed fields without the Lie
comparison, and D7 gives a Bruhat covering without disjointness.
The separate [dynamic update](dynamic-relative-progress.md) records
additional field and arbitrary-base obligations. The broader program,
including rational and general-base structure, remains incomplete.

## Verified proof publications, 21 November 2026

Both remaining targets from the 13 November update have published proofs.
Their Lean and Markdown pairs match the archived submissions at their
publication commits and in Library `a11d1e75f52192f694c9901f4b7fd7098b0f8ff9`.
The statement pairs also match the ones at the proof submissions' Library
bases. Two exact-type applications compiled with zero errors or warnings
over that current Library.

| Ledger entry | Exact theorem | Proof candidate and publication commit | Independent review task and exact-target validation receipt |
| --- | --- | --- | --- |
| C11, Task 6453 | `dynamicQuotientProper : DynamicQuotientProperStatement.{u}` | `3d9b328b-a689-4d58-a01b-6ace8b31d0d8` at `032961776f43ccd672c6266d265a9c644faeba13` | `6d48d57f-fa53-4614-a734-5b7593213345` and `7f02986a-03ee-4c66-906d-7aad48ad668c` |
| F, third interface, Task 6428 | `triangularDiagonalKernelTower : TriangularDiagonalKernelTowerStatement.{u}` | `0c7fd545-28ce-4ac7-9f07-91dbe42c9a79` at `af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e` | `e9e5dd07-1744-42c0-85bc-d5a73eab3bb9` and `13fd8441-ffaa-4328-a1f3-381970d58a3d` |

For C11 the theorem proves properness of the supplied `Q` over an
algebraically closed field of arbitrary characteristic. It retains all
test schemes in the right-coset equality and includes trivial and central
cocharacters. The proof uses affineness of a linear homogeneous quotient,
proved using geometric reductivity from the independent rank-one central
cover. A closed orbit in the affine quotient gives a closed immersion of
the supplied `Q` into the proper general linear dynamic quotient. The
independent review verified the type-and-value dependency audit against
Task 6453's exclusions.
[Statement](../../Langlands/GroupScheme/Dynamic/QuotientProperStatement.md),
[proof and dependency audit](../../Langlands/GroupScheme/Dynamic/QuotientProperProof.md).

For F the theorem constructs a tower for the supplied fppf diagonal
quotient `q : H ⟶ D(Λ)` of an affine locally finite type closed triangular
subgroup over any field. It retains every matrix size, including zero,
and permits torsion in the finitely generated abelian `Λ`. The proof
supplies `affineHomImage` and `affineNormalSubgroupQuotient` to
`TriangularLayer.admitsTower_diagonalizable_of_affine_image_and_normal_quotient`.
Each transition is an fppf quotient whose full kernel embeds as a closed
subgroup of `𝔾ₐ`. Conjugation factors through `D(Λ)`, and the kernel
embedding is equivariant for a character of `D(Λ)` on every test scheme.
This includes nonreduced kernels. The terminal map to `D(Λ)` is an
isomorphism.
[Statement](../../Langlands/GroupScheme/Absolute/TriangularDiagonalKernelTowerStatement.md),
[proof](../../Langlands/GroupScheme/Absolute/TriangularDiagonalKernelTowerProof.md).
