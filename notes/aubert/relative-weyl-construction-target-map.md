# General relative-Weyl constructions and finite targets: source map

This note maps the subgroup and finite-Coxeter prerequisites of the general
Aubert program to five Lean/Markdown pairs. It distinguishes constructed
objects and implemented helper proofs from proposition targets. It is the
finite and subgroup part of the source table for task
`e3d69272-2599-4a08-a934-cb11f2493e30`, not a completed table or proof of
Theorem 1.7 or Corollary 1.10. Their actual representation-functor and
Grothendieck-group specializations remain required.

The [general program source map](general-program-source-map.md) gives the
larger result families and correction policy. The
[Chapter V structural ledger](../renard/chapter-v-structural-inputs.md)
defines the S and D row identifiers used below. This note adds no external
structural row and does not turn a retained deduction into an assumption.

## Originals and conventions

The registered originals are:

- `aubert-1995-duality`, *Dualité dans le groupe de Grothendieck…*,
  printed pp.2180–2183 / one-based PDF pp.2–5, SHA256
  `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693`.
- `renard-2026-representations-groupes-reductifs-padiques`, French edition
  dated 9 July 2026, V.3.6–V.3.13 and V.4.1–V.4.6,
  printed pp.111–112 and 118–121 / one-based PDF pp.117–118 and 124–127, SHA256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The original passages and complete five Lean/Markdown pairs were read
directly. Aubert p.2180 actually prints the torus denominator in
`N_G(T0)/T0` and `N_(L_I)(T0)/T0`. The task instead requires the
full-centralizer convention at general reductive scope, explicitly given
by Renard V.4.1:
`W_G = N_G(A0)/Z_G(A0) = N_G(A0)/M0`.
The implementation follows that convention; it does not identify the two
denominators for an arbitrary reductive group.

Write `D(I,J)` for minimum-length representatives of `W_I w W_J`.
The source's `w_J` is the longest member of `D(J,empty)`, and
`J' = w_J^(-1)(J)`. Forward conjugation is `n L n^(-1)`;
the right/source intersection is `L_J ∩ n^(-1) L_I n`.
These directions are visible in the declarations.

The coefficient identity after Aubert (1.8), p.2182, cites Solomon through
Carter Proposition 2.7.7. This is distinct from the minimum-representative
result cited in Renard V.4.6(i), Carter Proposition 2.7.3, ledger S18.
No independent audit or proof of Carter or Solomon is claimed here.
The corrections to Aubert's later irreducibility argument are recorded in
the linked general source map; Proposition 3.2 supplies no evidence for
these constructions or their intended proofs.

## Actual subgroup quotients

The declarations in
[`RelativeWeyl`](../../Langlands/Group/RelativeWeyl.md) have prefix
`Langlands.Group.RelativeWeyl`. Their ambient parameters are only
`G : Type u`, `[Group G]`, and actual subgroups of `G`.
They require no topology, finiteness, root system or reductivity.

| Declarations | Constructed object or implemented proof | Additional hypotheses and source role |
| --- | --- | --- |
| `normalizer`, `centralizer`, `denominator`, `Weyl` | The actual subgroup normalizer and full centralizer, and their quotient `N_G(T)/Z_G(T)`. | None. Renard V.4.1, p.118 / PDF p.124. |
| `normalizerIn`, `denominatorIn`, `denominatorIn_normal`, `WeylIn` | Numerator `N_G(T) ∩ L`, restricted ambient centralizer denominator, its normality, and the subgroup quotient. | None. To interpret the denominator as the whole `Z_G(T)`, supply `Z_G(T) ≤ L`. |
| `inclusion`, `inclusion_mk`, `inclusion_eq_one_iff`, `inclusion_injective` | The homomorphism sending the class of an actual numerator element to its ambient class, its formula, and injectivity. | None. Elementary quotient construction underlying Renard V.4.3, p.119 / PDF p.125; it does not identify the image with a root-generated subgroup. |
| `intrinsicNormalizer_map` | The intrinsic normalizer in `L`, mapped into `G`, equals `normalizerIn T L`. | `T ≤ L`. |
| `centralizer_le_normalizerIn` | The full centralizer lies in that numerator. | `Z_G(T) ≤ L`. |
| `torusAction`, `torusAction_mk_apply`, `torusAction_injective` | Actual conjugation on `T` descends faithfully to the quotient; at `n` it sends `t` to `n*t*n⁻¹`. | None. This is an action on the subgroup `T`, not yet an identified action on relative roots or characters. |
| `conjugationEquiv`, `conjugationEquiv_apply` | Restrict actual conjugation by `g` to a multiplicative equivalence `L ≃* L'`, with its ambient formula. | The displayed actual equality `L.map (MulAut.conj g) = L'`. No continuity or representation transport is asserted. |
| `weylIn_centralizer_subsingleton` | The quotient for `L = Z_G(T)` is trivial. | None. This is the minimal-Levi quotient, not by itself ambient rank-zero triviality. |

The proofs use subgroup images, the normalizer's conjugation homomorphism
and its exact centralizer kernel, and elementary quotient elimination.
They implement group-level parts of D06. Specializing `T` and `L` to
the source's rational-point subgroups remains an actual realization
obligation.

## Intrinsic Coxeter objects

The declarations in
[`RelativeWeylIndexing`](../../Langlands/Group/RelativeWeylIndexing.md)
have prefix `Langlands.Group.RelativeWeylIndexing`. Their common parameters
are types `B,W`, `[Group W]`, `M : CoxeterMatrix B`, and
`cs : CoxeterSystem M W`. This is an actual Coxeter presentation of `W`.
Finiteness is required only where listed.

| Declarations | Constructed object or implemented proof | Further hypotheses |
| --- | --- | --- |
| `standardSubgroup`, `standardSubgroup_empty`, `standardSubgroup_mono`, `simple_mem_standardSubgroup` | Subgroup generated by `cs.simple '' I`, with empty, inclusion and generator laws. | None; the inclusion law takes `I ⊆ J`, and the generator law takes `i ∈ I`. |
| `standardSubgroup_univ` | All simple reflections generate `W`. | `[Fintype B]`. |
| `doubleCoset`, `mem_doubleCoset_self`, `mul_mem_doubleCoset` | The actual set `W_I w W_J`, its base member and stability under its two subgroup actions. | The stability law takes the displayed membership hypotheses. |
| `IsMinimal`, `isMinimal_one`, `isMinimal_inv` | Minimum length in the whole double coset, minimality of `1`, and inverse symmetry interchanging `I,J`. | No finiteness; the inverse law takes `IsMinimal cs I J w`. |
| `exists_minimal_in_doubleCoset`, `minimalReps`, `mem_minimalReps`, `minimalReps_nonempty` | Finite minimization supplies a minimum in each double coset; `minimalReps` filters `W` by that exact predicate. | `[Fintype W]`. Uniqueness is a separate target. |
| `longestRep`, `longestRep_mem`, `length_le_longestRep` | Choose a maximal-length member of `D(J,empty)` and prove membership and maximality. | `[Fintype W]`; the length bound takes membership in that same set. Uniqueness is not an input to the construction. |
| `conjugateStandardSubgroup`, `rightIntersection`, `intersectionSubset`, `intersectionSubset_subset` | Construct `w W_I w⁻¹`, `W_J ∩ w⁻¹ W_I w`, and its candidate simple-index subset of `J`. | None. The assertion that the candidate generates the intersection is separate. |
| `positiveSimpleSet`, `simpleImage`, `MapsIntoSimple` | Strict right-length increase; reflection labels occurring under conjugation; the requirement that every supplied simple index has an image in the stated target subset. | The first two need `[Fintype B]`; `MapsIntoSimple` does not. Reflection equality alone loses the root sign. |
| `associatedSubset` | Candidate `J'`, using `simpleImage cs (longestRep cs J)⁻¹ J`. | `[Fintype B]`, `[Fintype W]`. Its root and actual-Levi identifications are targets. |
| `ActualCoxeterSystem` | Fix the Coxeter group to `RelativeWeyl.Weyl T`, rather than an unrelated set of labels. | An actual group `G` and `T : Subgroup G`. It does not construct the required Coxeter system. |
| `eq_one_of_isEmpty`, `subsingleton_of_isEmpty`, `longestRep_eq_one_of_isEmpty` | Simple-reflection induction gives triviality of the ambient Coxeter group when its simple-index type is empty. | `[IsEmpty B]`; the last also needs `[Fintype W]`. For the actual quotient, the actual Coxeter realization must first be supplied. |

These constructions implement the objects on Aubert p.2180.
Finite minimization and maximization are internal arguments. They do not
prove the root/length comparison or the structural existence of the
actual Coxeter realization.

## Finite and realization proposition targets

[`RelativeWeylIndexingTargets`](../../Langlands/Group/RelativeWeylIndexingTargets.md)
uses the same namespace and intrinsic parameters. Every law in this table
is a Prop-valued definition, not a proof or a field assumed in construction
data. The separately listed multiplicity is a natural-number constructor.

| Declaration | Exact target or count | Further hypotheses and source boundary |
| --- | --- | --- |
| `minimalityLengthCriterion` | Whole-double-coset minimality iff strict left-simple length increase on `I` and strict right-simple increase on `J`. | No finiteness. Renard V.4.6(i), p.121 / PDF p.127, S18; comparison with roots also uses S17. |
| `minimalRepresentativeUnique` | Two minimal elements in the same specified double coset are equal. | No finiteness. Unique-minimum part of S18, distinct from the constructed finite existence proof. |
| `standardIntersection` | For minimal `w`, the right intersection is generated by `intersectionSubset cs I J w`. | No finiteness. Intrinsic Coxeter work behind D06 V.4.6(ii); S18 does not include every intersection assertion. |
| `intersectionMultiplicity` | Count `w ∈ D(I,J)` satisfying `W_J ∩ w⁻¹ W_I w = W_K`, with argument order `J,I,K`. | `[Fintype W]`. This is a Weyl-equality count; Aubert's count uses actual Levi equality. Their comparison is explicit below. |
| `solomonCancellation` | For every `K ⊆ J`, sum over all `I : Finset B` of `(-1)^|I| a_(J,I,K)` equals `(-1)^|K|`. | `[Fintype B]`, `[Fintype W]`. Integer coefficients; empty and full subsets included. Aubert p.2182 after (1.8), separate finite proof obligation. |
| `jacquetCancellation` | For `w ∈ D(J,empty)` and `K ⊆ J`, compute the signed sum over `I ⊆ positiveSimpleSet cs w` with `simpleImage cs w I ∩ J = K`. | `[Fintype B]`, `[Fintype W]`. Result is `(-1)^|K|` if every index of that positive set maps into simple indices of `J`, and zero otherwise. Aubert (1.9), p.2182; actual root interpretation still uses S17. |
| `longestRepresentativeUnique` | Every maximal-length member of `D(J,empty)` equals the constructed `longestRep cs J`. | `[Fintype W]`. Further finite Coxeter work; minimum uniqueness alone does not state it. |
| `longestSurvivor` | For `w ∈ D(J,empty)`, the full-image condition of the previous cancellation holds iff `w = longestRep cs J`. | `[Fintype B]`, `[Fintype W]`. Aubert pp.2182–2183. |
| `associatedSubsetLaws` | Inverse conjugation by `w_J` sends every index of `J` to a simple index; `|J'|=|J|`; `W_(J') = w_J⁻¹ W_J w_J`. | `[Fintype B]`, `[Fintype W]`. Root signs and actual Levis remain separate comparisons. |

The final three targets instead take an actual group `G`, `T : Subgroup G`,
`L : Finset B → Subgroup G`, and
`actual : ActualCoxeterSystem T M`. They state properties to realize for
the shared adapter's standard Levis, not properties of every arbitrary
family `L`.

| Declaration | Exact target | Further hypotheses and retained proof role |
| --- | --- | --- |
| `actualLeviWeylIdentification` | The range of the actual `RelativeWeyl.inclusion T (L I)` is `standardSubgroup actual I`. | No finiteness. D06 using the actual roots, S09/S13/S15. An injective quotient map alone does not establish this range equality. |
| `actualLeviIntersection` | For minimal `w` and every normalizer lift `n` of `w`, `L_J ∩ n⁻¹ L_I n = L_(intersectionSubset actual I J w)`. | No finiteness. D06 V.4.6(ii), with S14–S15 and the exact root/subset comparison. |
| `actualAssociatedLeviConjugation` | For every lift `n` of `w_J`, `n L_(J') n⁻¹ = L_J`. | `[Fintype B]`, `[Fintype (RelativeWeyl.Weyl T)]`. Associated-root and actual Levi comparisons under D06, with S14–S15. The direction is from `J'` to `J`. |

## Lift-independent actual subgroup action

[`RelativeWeylConjugation`](../../Langlands/Group/RelativeWeylConjugation.md)
uses prefix `Langlands.Group.RelativeWeyl`. Only `[Group G]` and actual
subgroups are needed, with the containments shown below.

| Declarations | Constructed object or implemented proof |
| --- | --- |
| `conjugateSubgroup`, `conjugateSubgroup_one`, `conjugateSubgroup_mul` | Actual forward subgroup image and its identity and product laws. |
| `conjugateSubgroup_eq_self` | An element of `L` preserves `L` under inner conjugation. |
| `conjugateSubgroup_centralizer`, `centralizer_le_conjugateSubgroup` | A normalizer element preserves the centralizer and sends every centralizer overgroup to another one. The second takes `Z_G(T) ≤ L`. |
| `conjugateSubgroup_eq_of_mk_eq` | Equal quotient classes give equal conjugate image subgroups when `Z_G(T) ≤ L`. The quotient relation puts `n⁻¹m` in `L`, and the inner-conjugation law proves equality. |
| `CentralizerOvergroup`, `weylConjugate`, `weylConjugate_mk`, `weylConjugationAction`, `mk_smul_overgroup` | Actual subgroups containing `Z_G(T)`, with a genuine action of `Weyl T`, defined by quotient descent and computed at every lift. |
| `inclusion_smul_overgroup` | The image of `WeylIn T L` fixes `L`, given `Z_G(T) ≤ L`. This proves stabilizer inclusion, not equality with the full stabilizer. |
| `weylTransporters`, `mem_weylTransporters_mk` | Construct `{w : Weyl T | w • L = L'}`, source first, target second, for centralizer overgroups, and identify membership with subgroup-image equality at a lift. |

This implements the elementary subgroup-level lift-independence argument
in Renard V.4.3, p.119 / PDF p.125, part of D06.
It does not equate the elementwise maps for different lifts: they can
differ by inner conjugation. Nor does it prove
`W(L,L)/W_L ≃ N_G(L)/L`; the latter still uses the actual
maximal-split-torus conjugacy and normalizer comparisons, S03/S08 and D06.

## Actual multiplicities and the equality-test bridge

[`RelativeWeylMultiplicityTargets`](../../Langlands/Group/RelativeWeylMultiplicityTargets.md)
uses prefix `Langlands.Group.RelativeWeylIndexing`. Here the family has type
`L : Finset B → RelativeWeyl.CentralizerOvergroup T`; pass
`fun H => (L H).val` to the earlier raw-family targets.

| Declaration | Constructed object, implemented helper or target | Additional hypotheses |
| --- | --- | --- |
| `actualRightIntersection`, `actualRightIntersection_mk` | Construct `L_J ∩ (w⁻¹ • L_I)` and expose `L_J ∩ n⁻¹ L_I n` at every lift. Independence comes from the quotient action. | No finiteness or Coxeter parameter is used by these two declarations. |
| `actualIntersectionMultiplicity` | Count minimum representatives satisfying equality of that actual subgroup with `L_K`, in source argument order `J,I,K`. | Actual Coxeter system and finite actual quotient. |
| `actualIntersectionEqualityCriterion` | For each minimum representative and `K ⊆ J`, actual equality `L_J ∩ w⁻¹ L_I w = L_K` iff generated-subgroup equality `W_J ∩ w⁻¹ W_I w = W_K`. | Actual Coxeter system; no finiteness. This is a realization target, not an instance or a new external structural assumption. |
| `actualMultiplicityComparison` | The actual and intrinsic counts agree for every `J,I,K` with `K ⊆ J`. | Actual Coxeter system and finite actual quotient. Prop target. |
| `actualMultiplicityComparison_of_equalityCriterion` | Prove that the pointwise criterion implies the count comparison, by equality of filtered finite sets and their cardinalities. | Same finiteness and a proof of the separately named criterion. This proves no instance of that criterion. |
| `actualSolomonCancellation` | The signed integer sum of actual Levi multiplicities is `(-1)^|K|` for `K ⊆ J`. | Finite `B`, finite actual quotient, actual Coxeter system. Prop target; no cancellation proof is supplied. |

These are the actual subgroup counts used after Aubert (1.8), p.2182.
A sufficient route to the pointwise criterion is to prove the earlier
actual and intrinsic intersection targets, then prove faithfulness of both
subset assignments `H ↦ L_H` and `H ↦ W_H`. Both equality tests then reduce
to `intersectionSubset I J w = K`. Quotient surjectivity connects the
earlier every-lift formula with `actualRightIntersection_mk`.
Those intersection and faithfulness results remain proof obligations;
the conditional cardinality helper supplies none of them.

## Required actual realization and proof owners

The intended specialization is to a connected reductive group over a
nonarchimedean local field, including positive characteristic, nonsplit
and nonquasisplit groups and the empty simple-root set. The generic
parameters above do not by themselves establish that specialization.

| Requirement still needed | Source and ownership |
| --- | --- |
| Identify actual rational points and the image `T0(F)`, and compare the scheme-defined normalizer and centralizer points with the abstract normalizer and centralizer of that image. Produce the quotient equivalence and compatibility of conjugation and root action. | The algebraic-groups/relative-roots owners, Workers 1107/207 and 1220/176, have received this requirement. The comparison is required over the infinite local fields in scope; no equality over arbitrary fields is inferred from notation. |
| Realize the reduced relative simple roots, finite quotient, simple reflections, actual Coxeter system, length and positive-root action. | S09/S13/S17, with the central summand retained. Relative-root owners 1220/176 coordinate with 1107/207; root/character owners 339/274 provide their shared lattice interfaces. |
| Construct the actual standard `P_I,L_I,U_I`, minimal Levi `L_empty=Z_G(T0)`, full Levi `L_S=G`, centralizer containment, faithful subset indexing and the root-group intersections. | S06/S14/S15 and the retained D06 deductions. Requirements are with 1107/207. The three actual targets and the equality-test criterion remain consuming proof obligations. |
| Compare `|J|` with `dim A0 - dim A_(L_J)` and `|S|-|J|` with `dim A_(L_J) - dim A_G`, retaining the empty case. | Renard V.3.6–V.3.7 and V.3.12–V.3.13, pp.111–112 / PDF pp.117–118. Retained D04 dimension comparisons using S09/S12, routed by Worker 1186 to 1220/176. The sign exponents are root-set cardinalities; the total split rank cannot replace them. |
| Identify length-defined positive sets and reflection-label images with the source's signed root images, including `J'=w_J⁻¹(J)`. | S17 plus the intrinsic minimum and associated-subset laws. These comparisons retain proof obligations under D06; reflection equality alone is insufficient. |
| Supply the rational-point and subgroup topologies, continuity of actual conjugation and the instances used by smooth representations. | S01/S04, routed to Worker 118, who directed the point-topology part to the Conrad program and Workers 105/208. Existing affine point-topology constructions are starting interfaces, not the whole subgroup realization. |
| Construct actual normalized functors, conjugation pullback along the inverse equivalence, exact K0 maps and normalization comparisons. | Shared adapter task `593ef603-6672-4424-976c-14e11e920d9c`, Worker 23 with transport owner 1180. Exactness and representation transport are representation-theoretic obligations, outside the external structural rows. |

For the sign comparison, strict right-length increase gives positivity of
`w α_i` by S17. Reflection equivariance together with positivity selects the
positive root from its reflection. For inverse associated subsets,
`longestRep_mem`, the minimum length criterion and inverse-length invariance
give positivity on `J` for `w_J⁻¹`, before applying the associated-subset
laws. This describes a route to prove, not an extra sign axiom.

The current published
[`GroupScheme.Rational.RelativeRoots`](../../Langlands/GroupScheme/Rational/RelativeRoots.md)
already constructs `Langlands.GroupScheme.relativeWeylGroup`,
`relativeRootSpan` and `relativeWeylAction`, with representative formulas.
Its normalizer/centralizer points are defined through scheme morphisms.
They are not definitionally the abstract subgroup normalizer/centralizer
used here. Its companion
[`Rational.Statement`](../../Langlands/GroupScheme/Rational/Statement.md)
defines `HasRelativeRootSystem` and `RelativeRootSystemStatement` as
propositions; their presence is not a proof or the required Coxeter bridge.
The comparison requirement preserves these existing owners and objects.

## Remaining representation targets and publication evidence

Worker 165 still owes the five actual class-level Theorem 1.7 targets and
the geometric-lemma K0 specialization using Worker 23's exact adapters;
Worker 14 owns the coordinated general geometric-lemma work.
Worker 1186 owns the Corollary 1.10 targets, including the relative-rank-one
length-two and Jacquet assertions, and the separately named Weyl-conjugacy
target for induced K0 classes. The last is representation theory behind
Aubert (1.2), not Chapter V structural data. Its classification and
character-independence dependencies must be recorded when instantiated.
Worker 76 owns the later proof tasks, final assembly and dependency matrix.
The operator remains the unadjusted sum `sum_I (-1)^|I| i_I r_I`;
none of these finite targets proves a representation identity for it.

At inspection on 2 November 2026, the first three pairs were independently
accepted and published in Library commit
`47cd8b71e79c9bb4aba6d9cc2664cb09fbff441c`:

| Pair | Candidate | Independent reviewer |
| --- | --- | --- |
| `RelativeWeyl` | `710b68e8-2925-45ef-976e-0eb5961fa051` | Reviewer 8594 |
| `RelativeWeylIndexing` | `fec609d4-e718-4c45-b5f6-9cf7b0567c21` | Reviewer 8622 |
| `RelativeWeylIndexingTargets` | `c17b0a7c-9355-4d4a-9273-53d767a9da2f` | Reviewer 8632 |

The next two had successful machine validation and independent semantic
approval but remained staged and unpublished at their inspection:
`RelativeWeylConjugation`, candidate
`e0f54c4d-be80-427c-b222-f91152e73cba`, Reviewer 8659; and
`RelativeWeylMultiplicityTargets`, candidate
`c1317573-5135-4aae-a15a-48e206331c14`, Reviewer 8665.
Integration order is quotient before indexing and conjugation, indexing
before indexing targets, and conjugation plus indexing targets before
multiplicity targets. These identifiers record evidence and do not name
mathematical imports.

Recovery check `6f5a9af5-594f-45d7-ae45-1ec8b23c4525` compiled all five
modules with no diagnostics and confirmed that
`actualIntersectionEqualityCriterion` returns `Prop`. This development
check is not independent proof acceptance. No completion of the host task
or proof of a declared target follows from these receipts.

Authors: Worker 165, with Worker 164's source-row analysis, subgroup-action
scope analysis and identification of the actual-Levi/Weyl equality-test gap,
and Worker 1186's rank/sign and actual-realization requirement refinements.
