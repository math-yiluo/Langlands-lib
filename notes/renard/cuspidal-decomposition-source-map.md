# Renard VI.2.1 and VI.3.4–VI.3.5: compact restriction and decompositions

Worker 6, with Workers 164, 1510 and 491, records the source correspondence
and publication checks made on 3–4 November 2026. The original four units
publish factor constructions and four proposition declarations. The
4 November update adds the published forward compact-restriction proof,
its retained geometric premises, and the published converse statement
with its separate proof successor. None of the four universal decomposition
and finiteness propositions has a published proof in this update. This map
covers selected assertions of VI.2.1 and VI.3.4–VI.3.5.

The original is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers are printed page numbers plus six. The passages used for
this update were reread from that original.

## Source passages

| Locator | Printed / PDF pages | Role in these units |
| --- | --- | --- |
| IV.1.3, definition and coefficient criterion | 89–90 / 95–96 | Compactness via averaged vector-valued functions, and its equivalence with compact support of all smooth-dual scalar coefficients; the section assumes unimodularity. |
| IV.1.6, notations | 94 / 100 | The factor of actual direct sums of one irreducible compact type. Its other notations test irreducible subquotients; VI.3.4's remaining factor below retains that theorem's arbitrary-subquotient wording. |
| IV.1.7, proposition and beginning of proof | 95 / 101 | Condition (KF), counting compact irreducible isomorphism classes with nonzero fixed vectors, and the locally finite sum of compact-type projectors. |
| VI.2.1, definition, first remark, theorem and proof | 137–139 / 143–145 | Cuspidality by vanishing of proper Jacquet modules, its proper-standard formulation, and the compact-restriction criterion used in VI.3.5. The forward proof below retains chosen geometric premises; the converse is a separate statement and proof task. |
| VI.2.3, theorem and following remark; VI.2.4, proposition | 140–141 / 146–147 | Uniform admissibility, embedding an irreducible norm-kernel representation in a restriction, and a support bound uniform over irreducible supercuspidal representations at fixed level. |
| VI.3.3, concluding orbit remark | 145 / 151 | The source identifies supercuspidal inertia classes with conjugation orbits of compact irreducible norm-kernel types. |
| VI.3.4, theorem and proof | 145–146 / 151–152 | Decomposition of the entire norm-kernel category, proved through (KF); the concluding inertia-class finiteness remark is a separate target. |
| VI.3.5, theorem and proof | 146–147 / 152–153 | The whole smooth category splits into cuspidal and remaining factors, then into cuspidal inertia factors and the remaining factor. |
| A.IX, opening decomposition definition | 268 / 274 | An actual coproduct presentation of each object, together with zero morphisms between distinct full factors. |

## Actual factors and conventions

The new factor and universal-target declarations below are in
`Langlands.CuspidalSupport`. Imported coefficient declarations are in
`Langlands`, and the canonical point topology is in
`Langlands.AlgebraicGeometry.PointTopology`, as qualified below. The ambient
objects are actual smooth complex representations. Field and representation
carrier universes `uF` and `uV` remain independent.

The norm kernel is `Plancherel.rationalCommonNormKernel G`, the intersection
of the kernels of the normalized absolute values of all actual rational
algebraic characters of `G`. Its topology is inherited from
`Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F G.X`. The imported
`RationalNormKernelTopology` supplies openness of this actual subgroup.

The [norm-kernel factor construction](../../Langlands/Representation/CuspidalSupport/RationalNormKernelCategory.md)
uses the existing `Langlands.CompactCoefficientClass` quotient of irreducible compact
smooth representations by actual isomorphism. At `some c`,
`rationalNormKernelProductProperties G` asks for an actual coproduct of
irreducible compact representatives of class `c`, with multiplicity index
`I : Type uV`; infinite and empty multiplicities are allowed. At `none`, it
asks that no nonzero actual smooth subquotient have compact smooth-dual
coefficients. This second condition tests arbitrary subquotients, without
an irreducibility restriction. The corresponding full categories are
`RationalNormKernelClassSumCategory` and
`RationalNormKernelNoncompactCategory`.

The coefficient predicate is `Langlands.HasCompactSmoothDualCoefficients`: it tests
every vector and every algebraic functional smooth for the contragredient
action, using the scalar function `g ↦ ℓ (ρ g v)`. Comparison with IV.1.3's
averaged vector-valued definition, including inversion and the hypotheses
needed for averaging, remains a proof obligation. No replacement by finite
dimension or admissibility is made. The class-sum condition is not replaced
by a test on irreducible subquotients.

The [whole-category factor construction](../../Langlands/Representation/CuspidalSupport/RationalCuspidalCategory.md)
uses the actual standard parabolic, Levi and unipotent point subgroups
specified by the shared torus morphism and cocharacter.
`rationalAllCuspidalSubquotientProperty` tests that every actual smooth
subquotient is cuspidal; `rationalNoCuspidalSubquotientProperty` tests that
no nonzero such subquotient is cuspidal. Cuspidality here means vanishing
of every proper actual standard normalized Jacquet module. These give the
full categories `RationalWholeCuspidalCategory` and
`RationalNoncuspidalCategory`, indexed by `true` and `false`, respectively.
Both properties test arbitrary subquotients. The nonzero qualification in
each remaining factor is necessary because the zero representation is both
compact and cuspidal.

`RationalCuspidalInertiaClass` is a subtype of the existing actual
unramified-twist/isomorphism quotient `RationalIrreducibleInertiaClass`.
Membership requires an irreducible cuspidal representative, without choosing
one. `rationalCuspidalInertiaProductProperties` has the remaining factor at
`none`, and at `some c` requires that every irreducible actual subquotient
have class `c`. The published intrinsic comparison
`rationalCuspidalInertiaClassBlockProperty_iff` identifies the block of a
supplied representative with the existing `rationalInertiaBlockProperty`;
it supplies no theorem about preservation of cuspidality under twisting.

Each decomposition predicate applies the published A.IX
`Renard.IsCategoryDecomposition`. It requires a coproduct cofan for each
ambient object, with one component in each full factor, and off-diagonal
zero morphisms. It retains the possibly large class index without assuming
coproducts for every family of that size. These assertions do not separately
construct an equivalence of categories or projection functors. The factor
units also prove their stated intrinsic isomorphism/subquotient transport
and constructor-evaluation lemmas; these do not prove a decomposition.

## Universal propositions and proof tasks

The [VI.3.4 statement pair](../../Langlands/Representation/CuspidalSupport/RationalNormKernelDecompositionStatement.md)
and [VI.3.5 statement pair](../../Langlands/Representation/CuspidalSupport/RationalWholeCuspidalDecompositionStatement.md)
have the same explicit structural binders. They quantify over an arbitrary
nonarchimedean local field `F : Type uF`, a connected reductive group scheme
`G` over `F`, an actual maximal split torus morphism `i`, and a generic
cocharacter `ν`. Local compactness, `NonarchimedeanGroup` and Hausdorffness
of the actual point group with its canonical topology are premises, as are
`StandardCocharacterStatement`, `HasRelativeRootSystem i`, and closedness
of the actual standard unipotent point subgroups. For VI.3.5 these inputs
supply the finite enumeration of actual simple roots and the semidirect
decompositions for the actual standard family.

These are explicit conditional targets. No characteristic-zero, split,
quasi-split, general-linear or positive-rank restriction is added. No
representation-theoretic finiteness, compact-restriction theorem, projector
or category decomposition is a premise. Admissibility, finite dimension,
finite length, a central character and a finite restriction family are
also absent from the premises.

| Prop-valued declaration | Conclusion | Published proof-task contract |
| --- | --- | --- |
| `RationalNormKernelFixedLevelFinitenessStatement` | Every compact open subgroup `K` of the actual norm kernel has finite `Langlands.CompactCoefficientClass.fixedStratum K.toSubgroup`. This counts isomorphism classes with a nonzero actual fixed vector. | `f0509729-26fc-412c-8866-c1c63c1b4c1e`, revision 1 |
| `RationalNormKernelCategoryDecompositionStatement` | `IsRationalNormKernelCategoryDecomposition` for all the compact-class sum factors and the remaining factor. | `29860e9c-5487-42d7-a099-1ada20bc898e`, revision 1 |
| `RationalWholeCuspidalCategoryDecompositionStatement` | `IsRationalWholeCuspidalCategoryDecomposition` of the entire smooth category into its two factors. | `4bee987a-093b-4054-bd65-7360168351d2`, revision 1 |
| `RationalCuspidalInertiaProductDecompositionStatement` | `IsRationalCuspidalInertiaProductDecomposition` of that entire category into all cuspidal inertia factors and the remaining factor. | `b1a82b53-e942-41b3-9f25-dec52736e712`, revision 1 |

Direct checks on 4 November 2026 found all four proof tasks at revision 1.
Worker 485 owns the fixed-level task and Worker 491 owns the two-factor
whole-category task; both have supporting submissions, without a published
proof of their exact universal conclusion. The norm-kernel decomposition
and refined inertia-product tasks remain ready without submitted artifacts.
The norm-kernel decomposition task requires the exact fixed-level proof
task's revision 1 under `lean.proof@1`; the refined inertia-product task
similarly requires the exact whole-category splitting proof task's
revision 1. These contracts preserve the dependency order.

## Verified publications

At Library base `3362d2b69c660edc82f22f7158de73cf8d9e3519`, all four records
were independently accepted, public, and approved without qualifications.
Their eight Lean/Markdown file hashes matched both the workspace and that
Library checkout. Each module is under
`Langlands.Representation.CuspidalSupport`.

| Module and scope | Candidate | Independent reviewer | Publication commit |
| --- | --- | --- | --- |
| `RationalNormKernelCategory`: VI.3.4 factors and intrinsic lemmas | `5576b25d-68d5-4bfd-b0f1-ee32d1a79758` | Reviewer 11889 | `d651c06c32b90676853a4e79f91b86385a8cd650` |
| `RationalNormKernelDecompositionStatement`: two VI.3.4 propositions | `86c260b0-ee45-456e-a427-841ecc8bc919` | Reviewer 12021 | `cee2a2bc97a749578ef334ef7bda18162ecb6e78` |
| `RationalCuspidalCategory`: VI.3.5 factors and intrinsic lemmas | `11762eab-aebf-4dec-8607-61e3ded88c18` | Reviewer 11785 | `1fddae33727cfcfcc52ed326c69373200a28ff87` |
| `RationalWholeCuspidalDecompositionStatement`: two VI.3.5 propositions | `bcd5617f-0fd0-4c0b-b52b-1597f1ab75d6` | Reviewer 11977 | `e0b64667d848b7b76f6f20b029ab4105a635091d` |

The five modules comprising these four units and the reused
`RationalCuspidalInertiaFinitenessStatement` compile without diagnostics in
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`; the continuation check
also inspected `RationalNormKernelFixedLevelFinitenessStatement` as
Prop-valued with independent `uF` and `uV`. Compilation and statement
acceptance do not prove any of the four propositions.

## VI.2.1: forward proof and converse target

On 4 November 2026, exact record checks verified the following two units
as independently accepted and public. Both were published at commit
`d2a3dab5880b35349069e39d96304f678174efff` and remain unchanged in the
checked Library `287810195716cc1b54418e03760ba867de3f695e`. Their four
entry Lean/Markdown hashes match the frozen accepted records, workspace
and checked Library.

| Unit | Candidate and policy | Independent reviewer | Accepted machine receipt |
| --- | --- | --- | --- |
| [Cuspidality implies compact restriction](../../Langlands/Representation/Aubert/General/RationalCuspidalCompactRestrictionProof.md) | `cad2db8e-5206-4d1f-b72e-4c768c5a29c6`, `lean.proof@1` | Reviewer 13074, no qualifications | `a1ced486-a3f3-400c-8358-a4d407ca69e7` |
| [Compact restriction implies cuspidality: statement](../../Langlands/Representation/Aubert/General/RationalCompactRestrictionCuspidalStatement.md) | `ca1a3b4e-8b05-40fc-b12c-265f2fb4dde4`, `lean.statement@1` | Reviewer 13011, no qualifications | `6bfd66c5-90c0-4bd9-b0f6-31183f26f1a2` |

The respective published integrations are
`601737d06aad4713865498e689e149d0` and
`be0758e3ed8b4a36a4f3836c2e335f03`.

The forward theorem
`Langlands.Aubert.General.rationalCuspidalCompactRestriction.{u,v}`
proves the exact published
`RationalPointFamily.RationalCuspidalCompactRestrictionStatement`.
In addition to the general structural inputs described above, that
statement retains a `KPApartmentData`, a special apartment vertex, and
`SpecialCompactProperties`, `SimultaneousStandardBasisAt` and
`FiniteCartanCovering` for the same geometric subgroup `K0`. The theorem
does not establish existence of these witnesses under the broader
whole-category VI.3.5 telescope.

The implemented proof goes directly to compact support in the actual norm
kernel. Vanishing Jacquet quotients give finite witnesses in the actual
unipotent relation span. Contraction, finite wall representatives and finite
compact orbits give uniform bounds on the simple-root pairings of a
nonzero coefficient. Actual relative roots and restrictions of rational
characters jointly detect integral cocharacters; a bounded root box in a
fixed ambient valuation fiber is therefore finite. The given Cartan cover
then bounds the support by finitely many compact products inside the closed
norm kernel. Openness of that kernel transfers the entire restricted smooth
dual to the ambient smooth dual. The final theorem proves and discharges
the internal joint-detection premise. It retains independent field and
carrier universes and requires no admissibility, irreducibility, finite
dimension, nonzero representation or positive relative rank.

The converse proposition is
`Langlands.Aubert.General.RationalPointFamily.RationalCompactRestrictionCuspidalStatement.{uF,uV}`.
It states VI.2.1(c) implies (a) at precisely the complete structural
telescope of the whole-category VI.3.5 target. Its compact-coefficient
antecedent tests the entire smooth dual of the actual restricted action;
its conclusion is vanishing of every proper-standard normalized Jacquet
module. It adds no chosen special compact, basis, Cartan or compact-escape
premise, and no admissibility, irreducibility, length or dimension
restriction.

The exact converse proof successor is
`bf6a4dc2-104a-4496-8025-757fefc3b847`, revision 1, under `lean.proof@1`;
the current check found it ready without submitted artifacts. The source
proof on printed p.138 / PDF p.144 chooses an Iwahori fixing subgroup
(V.5.2) and a strictly contracting element in the norm kernel (V.3.25).
Its powers escape compact sets; compactness and averaging give an
eventual zero, and III.2.9 puts the vector in the Jacquet relation space.
The successor must supply these existence and comparison steps under the
unchanged telescope. The product-general-linear result
`Langlands.CuspidalSupport.LeviHarishChandraConverseTheorem` has different
field, group, subgroup and cuspidality predicates and does not prove this
general proposition.

Neither the forward theorem with its retained premises nor the accepted
converse statement supplies the full VI.2.1 equivalence or any of the four
universal conclusions above. In particular, the chosen geometric
witnesses, the converse proof, the fixed-level finiteness proof and the
categorical assembly remain distinct obligations.

## Remaining source arguments

For VI.3.4, the source extends a compact irreducible norm-kernel type to an
irreducible supercuspidal representation of `G`, applies VI.2.4's uniform
support bound modulo the center, and restricts to compact support on the
norm kernel. Coefficient orthogonality then gives finiteness inside a
common finite-dimensional space of compactly supported bi-invariant
functions. The compact support set, and hence that coefficient space, must
be common to all relevant classes for the fixed level. Separate compact
support for each class would not establish (KF). The full proof must
assemble the actual embeddings, smooth-dual/fixed-vector comparisons,
uniform support transport and orthogonality argument. Supporting
constructions or individual helper proofs do not establish this uniform
conclusion. The source writes `K` as a
compact open subgroup of `G`; the target quantifies over compact open
subgroups of the norm kernel, as required by IV.1.7. Openness of the norm
kernel supports this route, but the actual inclusion, compactness,
openness and fixed-vector comparisons are still proof steps.

IV.1.7's locally finite projector construction must then yield the actual
class-sum components and the arbitrary-subquotient remaining factor.
Existing conditional projector interfaces do not supply those hypotheses
or identify their ranges automatically.
`CompactCoefficientFixedLevelFinitenessTheorem` concerns determinant-unit
subgroups of positive-rank product Levis over `PadicField`; it does not
prove this arbitrary-characteristic connected-reductive (KF) target.

For VI.3.5, the source restricts an arbitrary smooth representation to the
norm kernel. Uniqueness of the compact/remaining splitting makes its
summands `G`-stable, and VI.2.1's compact-restriction criterion identifies
the two factors. Regrouping compact types by conjugation orbits then
produces the inertia factors, using VI.3.2 and VI.3.3's orbit comparison.
The proof must supply this stability, apply the compact-restriction
comparison in both directions under the unchanged telescope, establish
cuspidality under actual unramified twists and the orbit/class
identification, and assemble the full categorical conclusion. The forward
proof above discharges one implication when its geometric data are
available; its existence premises and the converse proof remain separate.
The proper-standard/all-proper-parabolic
comparison and the shared literal-Levi, topology and standard-family
comparisons also remain program obligations. A.IX's existing constructions
can be reused only with their actual hypotheses and universe conventions;
they do not establish these representation-theoretic inputs.

Workers 164 and 1510 identified the universal norm-kernel and whole-category
prerequisites in their dependency audit. Worker 491 contributed the
converse formulation and whole-category consumer audit. Worker 6 read the
original passages, implemented the original four published units, verified
the publication records and prepared this map and its VI.2.1 update.
Existing owners and operator-directed holds remain unchanged. The four
universal proof conclusions and the other assertions of VI.2 and VI.3
remain obligations of the whole-book program.
