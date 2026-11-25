# General Aubert formal identities: target and dependency map

This page maps the 36 declarations in the eight representation-side
construction/target pairs of the general relative-Weyl modules of the general
Aubert duality program.
It complements the [84-declaration finite/subgroup table](relative-weyl-construction-target-map.md)
and the broader [general program source map](general-program-source-map.md).
The tables distinguish actual constructions and elementary helper proofs from
Prop targets. They do not assert any main identity, supply the missing
connected-reductive realization, or declare these modules complete.

All representation-side names below have prefix `Langlands.Aubert.General`.
The actual normalized functor and operator adapters belong to the
[adapter modules](general-adapter-dependency-table.md); their files were
inspected as dependencies. Later upstream interface or meaning changes
require reconciliation. All the pairs of this page, the adapters and the
geometric pair are now in the Library.

## Common actual data and named prerequisites

The main statements take a group with `Group`, `TopologicalSpace`,
`LocallyCompactSpace` and `NonarchimedeanGroup` structures; the last includes
the topological-group structure. The finite type `ι` indexes simple relative
roots at specialization. It may be empty. `P`, `M`, `U` are families of
actual `Subgroup G` values indexed by `Finset ι`. The visible data are
semidirect decompositions `P I = M I ⋉ U I` and closedness of every radical.
The statements themselves do not certify that these families are standard
rational-point parabolics.

Every K0 is the published exact group
`SmoothRep.FiniteLengthGrothendieckGroup.{0,uG,max uG uV} ℂ H`.
It uses isomorphism classes of actual smooth complex representations of finite
group-algebra length and relations from all actual short exact sequences,
including nonsplit sequences. It is not a free group on unrelated labels.
The saturated carrier universe makes induction/Jacquet composites endomorphisms.
The full smooth categories are retained for the underlying functors.
Representation carriers are `Type (max uG uV)`; the exact K0 group itself
lives in `Type (max uG ((max uG uV) + 1))`, as follows from its
isomorphism-class quotient construction.

`ParabolicFiniteLength h hU` is the conjunction of finite-length preservation
and preservation of finite-length short exact sequences for each actual
normalized induction and Jacquet functor. The maps `inductionK0` and
`jacquetK0` are the published generic exact-functor maps with these
prerequisites. Their class formulas use the actual functor objects and the
supplied preservation proofs.

The unadjusted operator is exactly
`alternatingOperator P M U h hU hfl = ∑_I (-1)^|I| i_I r_I`.
No cuspidal-support sign is applied. The upstream class formula gives
`D_G[A] = ∑_I (-1)^|I| [i_I(r_I A)]`. When `ι` is empty it has the single
term `i_∅ r_∅` of sign `+1`; identifying that term with the identity is
additional actual-family work.

For Levi operators the inputs also include closedness `hM J`, the actual
restricted decompositions `hLevi J I` inside `M J`, and their named
preservation hypotheses `hLeviFl`. `leviIndex J I` is the cardinality-preserving
subtype embedding. `leviAlternatingOperator` uses the same ambient subgroups
restricted by `subgroupOf (M J)`, indexed by `Finset J`.

Induction uses the positive half Haar modulus, and Jacquet restriction uses
the inverse half modulus on actual unipotent coinvariants. Actual forward
subgroup conjugation by `n` gives representation transport by inverse
pullback, with action `σ(n⁻¹ x n)`. Its exact-K0 map is unconditional.
The contragredient map additionally takes `CompactOpenCofinal G` and
`ContragredientPreservesFiniteLength G`; its exact-additivity construction
uses the published smooth-contragredient short-exactness theorem.

## The five Theorem 1.7 targets

These seven declarations occur in five individual pairs. Each target returns
`Prop`; no field of its construction data supplies its desired equality.
The formulas are equalities of integer-linear maps on whole exact K0 groups,
except the explicitly quantified actual-class eigenvalue.

| Pair and declarations | Exact source assertion or internal helper | Further visible inputs and remaining work |
| --- | --- | --- |
| [ContragredientTarget](../../Langlands/Representation/Aubert/General/ContragredientTarget.md): `ContragredientCommutationStatement` | Theorem 1.7(1), printed p.2181: `D_G ∘ c_G = c_G ∘ D_G`. | The common ambient preservation premises, compact-open cofinality and smooth-contragredient finite length. The actual reductive instance and compatibility proof remain required. |
| [InductionTarget](../../Langlands/Representation/Aubert/General/InductionTarget.md): `InductionCompatibilityStatement` | First equation of Theorem 1.7(2): for every `J`, `D_G ∘ i_J = i_J ∘ D_(M J)`. There is no extra rank sign. | The closed-Levi, restricted-decomposition and Levi-preservation data above. Transitivity, geometric expansion, cancellation and induced-class conjugacy belong to the intended proof, not construction fields. |
| [JacquetTarget](../../Langlands/Representation/Aubert/General/JacquetTarget.md): `conjugationMembership_of_map_eq` | Internal elementary helper converting `L.map (conj n) = N` to `x ∈ N ↔ n⁻¹ x n ∈ L`. | Only actual subgroups and a group structure. Its proof uses an actual image preimage and inverse cancellation; it proves no K0 identity. |
| Same pair: `JacquetCompatibilityStatement` | Second equation of Theorem 1.7(2): `r_J ∘ D_G = Ad(w_J) ∘ D_(M J') ∘ r_J'`. | An actual finite quotient `N_G(T)/Z_G(T)` with a Coxeter system, its `longestRep` in `D(J,∅)`, `associatedSubset = w_J⁻¹(J)`, and the separate `actualAssociatedLeviConjugation` prerequisite. Every normalizer lift is quantified. The helper supplies the actual continuous inverse pullback domain. Relative-root positivity, standard-family realization and the identity proof remain required. |
| [InvolutivityTarget](../../Langlands/Representation/Aubert/General/InvolutivityTarget.md): `InvolutivityStatement` | Theorem 1.7(3): `D_G ∘ D_G = id` on the whole group. | Only the common construction prerequisites. No involutivity premise or proof is supplied. |
| [CuspidalEigenvalueTarget](../../Langlands/Representation/Aubert/General/CuspidalEigenvalueTarget.md): `IsStandardCuspidal` | Internal extension of the vanishing condition before Notation 1.6 on p.2181: every proper standard normalized Jacquet object is `CategoryTheory.Limits.IsZero`. | This predicate is on the full smooth category. Irreducibility is separate. It includes no admissibility conjunct; comparison with GL/BZ's admissible-cuspidal predicate is a separate obligation. |
| Same pair: `CuspidalEigenvalueStatement` | Theorem 1.7(4): for actual irreducible cuspidal `A`, `D_G[A] = (-1)^|S|[A]`. | Irreducibility remains explicit and supplies finite length by published `SmoothRep.hasFiniteLength_of_isIrreducible`. The full-subset identity term, actual simple-root cardinality and eigenvalue proof remain required. |

The source's `w_J` is the longest member of `D(J,∅)`, not an unspecified
longest Weyl element. Forward transport carries `M J'` to `M J`.
Conjugate subgroup images can be independent of the lift without the
elementwise conjugation maps being equal. The all-lifts statement does not
assume such elementwise independence.

## Geometric-lemma construction and target

The 17 declarations of
[GeometricK0Target](../../Langlands/Representation/Aubert/General/GeometricK0Target.md)
implement the actual normalized terms of Aubert (1.3), p.2181.
For output subset `I`, input subset `J` and a lift `n` of `w ∈ D(I,J)`,
the six subgroups are fixed:

| Role | Source inside `M J` | Target inside `M I` |
| --- | --- | --- |
| Levi | `M J ∩ n⁻¹(M I)n` | `M I ∩ n(M J)n⁻¹` |
| Parabolic | `M J ∩ n⁻¹(P I)n` | `M I ∩ n(P J)n⁻¹` |
| Radical | `M J ∩ n⁻¹(U I)n` | `M I ∩ n(U J)n⁻¹` |

| Declarations | Implemented construction, helper or target | Precise premises and proof boundary |
| --- | --- | --- |
| `geometricSourceIntersection`, `geometricTargetIntersection` | Actual subgroup intersection and image under inverse/forward `MulAut.conj`. | Only a group and actual subgroups. No minimum-representative hypothesis is needed merely to form them. |
| `geometricIntersectionMembership` | Proved membership equivalence for inverse conjugation from the target Levi to the source Levi. | Expands subgroup-image membership, cancels inverses and interchanges the two conjuncts. |
| `isClosed_map_conj`, `isClosed_geometricSourceIntersection`, `isClosed_geometricTargetIntersection` | Proved closedness laws in a topological group. | Closedness of the input factors; conjugate image is a preimage under a continuous conjugation map. |
| `GeometricSourceDecomposition`, `GeometricTargetDecomposition` | Separate Prop predicates for the actual semidirect decompositions of the displayed parabolics, in their ambient Levi subgroups. | No arbitrary replacement of the displayed intersection Levi or radical is allowed. No instance is proved. |
| `geometricSourceJacquetFunctor`, `geometricTargetInductionFunctor` | Actual normalized Levi-in-Levi functors of the upstream adapter, specialized to these subgroups. | Closed ambient Levis/radicals and the displayed source/target decompositions. Closedness of the intersection radicals is derived. |
| `geometricTermFunctor` | Actual full-smooth composite: source Jacquet restriction, forward-`n` representation transport by inverse pullback, then target induction. | Same actual subgroup data, at saturated carrier universe. |
| `GeometricTermFiniteLength` | Named four-part prerequisite: finite-length preservation and finite-length short-exact preservation for the source Jacquet and target induction functors. | These are representation-theoretic obligations. Continuous-equivalence conjugation preservation is already published. |
| `geometricTermK0` | Composite of the actual exact-K0 source/target maps and `conjugationK0`. | Takes exactly those preservation premises, with no expansion equation supplied. |
| `geometricTerm_hasFiniteLength`, `geometricTermK0_ofRepresentation` | Derived length witness and proved actual-class formula for that composite. | Uses source preservation, published pullback preservation, target preservation and the three actual generator formulas. It proves no geometric lemma. |
| `GeometricIntersectionDecompositions` | Separate realization proposition for both actual decompositions at every minimum representative and every lift. | Its connected-reductive instance remains required. It contains no class equation. |
| `GeometricK0ExpansionStatement` | Separate Prop target `r_I ∘ i_J = ∑_(w∈D(I,J)) geometricTermK0(w)`. | Uses the actual finite normalizer/full-centralizer quotient, its Coxeter indexing, the displayed decomposition proposition and term preservation premises. Every quotient section is quantified; choice and quotient surjectivity supply such sections. No expansion proof is supplied. |

The actual geometric filtration and orbit functors are separate work. The
orientation inspected for it sends `w` to `P_J * n⁻¹ * P_I` on
`P_J \ G / P_I`, so the inversion comparison with `W_I \ W / W_J`
must be proved. Both actual Haar correction twists, smooth realization,
graded-piece identification, parabolic normalization and any compact/full
induction comparison remain necessary. Trivial input characters do not remove
the Haar corrections.

The published `SmoothRep.filtrationGrothendieckStatement` and its proof
already derive exact K0 additivity and piece finite length from actual smooth
gluing and finite length of the total object. This target does not duplicate
that theorem or pretend the missing specialization is an arbitrary sum of
maps. No new checked general interface for it was recorded.

The elementary intersections also overlap the published
`Langlands.Geometric.intersectionSource`, `intersectionTarget` and
`intersectionConjugation`, and the `Geometric.GeneralIntersections` subtype
and continuous-conjugation constructions. Their comap convention and the
literal image convention used here are not definitionally interchangeable in
dependent functor arguments; reuse across them needs equality and transport
bridges. Those elementary constructions do not supply the normalized
intersection-term K0 expansion target.

## Corollary 1.10 and its representation prerequisites

The module
[GeneralCorollaryTargets](../../Langlands/Representation/Aubert/GeneralCorollaryTargets.md)
contains ten declarations. The normalization and ambient preservation
premises are the same as above. Its `IsCorollaryLeviCuspidal` uses the actual
restricted normalized Jacquet objects inside the closed Levi.

| Declaration | Exact assertion or internal construction | Remaining source-to-proof obligation |
| --- | --- | --- |
| `HasTwoConstituents` | Two actual irreducible smooth representations and an actual short exact sequence with them as factors, in either order. | It neither asserts existence nor assumes splitting. Exact K0 additivity is already published. |
| `IsMaximalStandard` | `J = univ.erase α` for a simple root `α`. | Its relative-corank-one interpretation uses actual rank comparisons. It has no instance for an empty root type. |
| `IsCorollaryLeviCuspidal` | Every proper standard normalized Jacquet object in `M J` is zero. | Actual standard/Levi-in-Levi realization; irreducibility is a separate hypothesis. |
| `corollary110a` | For irreducible cuspidal `σ` with irreducible actual induction, `D_G[i_J σ] = (-1)^|J|[i_J σ]`. | Retains the source irreducibility hypothesis. Theorem 1.7 induction compatibility and the Levi eigenvalue give the intended proof. |
| `ConstituentExchange` | Both equations exchanging two actual constituent classes under `(-1)^|J| D_G`. | This is the conclusion predicate, not a supplied law of the operator. |
| `rankOneLengthTwo` | Reducibility of the actual cuspidal induction from a maximal standard Levi implies an actual length-two composition series. | Casselman Corollary 7.1.2 gives length at most two under his admissible/absolutely-cuspidal setting. General admissibility, the cuspidality comparison, nonzero induction, finite length and actual factor realization must be discharged. |
| `rankOneSelfAssociation` | In the same reducible case, `associatedSubset actual J = J` and every specified longest lift normalizes the actual Levi. | Casselman Theorem 7.1.4 gives irreducibility in the non-self-dual case. Its contrapositive, standard-root identification and the actual associated-Levi comparison require proof. This deduction is not an external structural row. |
| `RankOneJacquetPattern` | `r_J ρplus ≅ σ`, `r_J ρminus ≅ Ad(n⁻¹)σ`, and every other proper standard Jacquet module of both constituents is zero. | Uses actual categorical isomorphisms and object-level vanishing, with action `σ(n x n⁻¹)` for `Ad(n⁻¹)`. |
| `rankOneJacquetModules` | Existence of actual constituents with that pattern, for every specified longest lift and its normalizing proof. | Length two, self-association, geometric lemma, cuspidal-support detection and exactness remain separate representation-theoretic work. |
| `corollary110b` | Reducible induction of irreducible cuspidal `σ` from `J = S \ {α}` has two irreducible factors exchanged by `(-1)^|J| D_G`. | The actual length-two series and both class equations occur in the conclusion. Assemble the named prerequisites, full-subset term, exact additivity and induced-class Weyl conjugacy. |

The sign in part (b) is `(-1)^|J|`, not `(-1)^|S|`. The latter occurs
in the top term of its proof, where maximality gives `|S| = |J| + 1`.
Part (a) includes `J = ∅`; part (b) is vacuous if there are no simple roots.
No GL-specific tempered-induction irreducibility theorem replaces these
general prerequisites.

## Separately named Weyl conjugacy and classification dependence

The module
[GeneralWeylConjugacyTarget](../../Langlands/Representation/Aubert/GeneralWeylConjugacyTarget.md)
has the remaining two declarations:

| Declaration | Exact target | Required proof boundary |
| --- | --- | --- |
| `inducedK0WeylConjugacy` | `i_J ∘ Ad(n) = i_I` on exact K0 whenever an actual normalizer element conjugates `M I` onto `M J`. | Actual normalized maps, every such normalizer element and the actual inverse-pullback transport. No induced-representation isomorphism is asserted. |
| `inducedClassWeylConjugacy` | Equality of the classes of the two actual normalized induced modules on every finite-length input. | Transport finite length follows from published continuous-equivalence pullback preservation. The comparison with the map-level target uses the existing generator formulas and `hom_ext_object`; that equivalence is not proved in this pair. |

These express Aubert (1.2), p.2181, cited there to
Bernstein–Deligne–Kazhdan Lemma 5.4(iii), and Ban–Jantzen Proposition 4.1(3),
p.158. Ban–Jantzen's proof explicitly uses character independence, Langlands
classification and the geometric lemma. That route is allowed in the
standalone general program. It is not classification-independent merely
because the target omits a classification premise.

No general classification or character-independence theorem has been adopted
here as an exact proof dependency: these are target declarations, with no
Weyl-conjugacy proof. Any proof using that route must identify its actual
general declarations and hypotheses. The inspected GL-specific
`Langlands.PadicField.TopologicalData.TemperedLanglandsDatum.langlandsQuotient`
is a head construction and does not supply the required general classification
theorem. This unfilled dependency cannot be moved into the external structural
list or counted as a discharged representation premise.

## Actual realization and proof obligations

The final source scope is connected reductive rational-point groups over
nonarchimedean local fields, including the permitted positive-characteristic,
nonsplit, non-quasisplit and empty-root cases. The generic signatures add no
restriction excluding those cases, but do not construct them.

| Required comparison or result | Construction or target, and boundary |
| --- | --- |
| Actual rational-point topology, standard `P_I`, `M_I`, `U_I`, Levi decompositions and closedness | Shared with the Renard, algebraic-group and Kaletha–Prasad work; the adapter modules specialize the actual adapters. The [Chapter V ledger](../renard/chapter-v-structural-inputs.md) remains the itemized external boundary. |
| `M_∅ = Z_G(T0)`, subgroup quotient inclusion and relative-root action | The finite/subgroup table constructs the actual abstract quotient and inclusion. Scheme-morphism normalizer/centralizer points still require comparison with abstract rational-point subgroups. |
| Coxeter/simple-root realization, positive-root signs, minimum and longest representatives, actual standard-Levi intersections | Intrinsic constructions and distinct realization/cancellation targets are in the finite/subgroup table. Equality of conjugated reflections loses root signs. No quotient injection alone proves the actual Levi/Weyl equality test. |
| Rank and central directions | Retain `|J| = dim A0 - dim A_(M J)` and `|S|-|J| = dim A_(M J)-dim A_G`. Total split rank cannot replace these exponents. These comparisons and the retained D04/D06 deductions are not extra external fields. |
| Exactness, finite length, admissibility, transitivity, duality and normalization | The adapter modules expose the named prerequisites; the general program must supply their representation-theoretic proofs or exact published reuse. |
| Actual geometric filtration and normalized smooth graded-piece comparison | Separate geometric work, with the Renard formalization; these modules supply the actual normalized K0 target and elementary term constructions. |
| Length two, self-association, Jacquet constituent pattern and induced-class conjugacy | The Corollary and Weyl-conjugacy modules supply the targets; their proofs and the final assembly belong to the general program (see the [dependency matrix](general-program-dependency-matrix.md)). |
| Main identities and their general-to-GL comparison | The five individual targets above retain the general scope; the existing GL results and the general-to-GL comparison modules are preserved. No generic predicate is a drop-in replacement for the established GL operator without the actual indexing/functor/group comparison. |

The structural work planned as of 2 November 2026 covered simple roots, choice-free standard
families, subgroup Weyl data and rational decompositions, expressly
excluding Coxeter/length/minimum-representative work, and a rank-zero
scalar-torus correction: nonempty rank for the scalar torus, positive rank
for its scalar split-component claim, and the separate trivial `GL_0` split
component. These plans are not proofs.

A later version of the adapters, now in the Library, retains the earlier
definitions and adds helper lemmas. Its additional `DynamicParabolic` pair supplies
`dynamic_isSemidirectDecomposition` and `dynamic_projection_eq_limitHom`
for dynamic cocharacter subgroups on every test scheme, including rational
points at the identity test object. It fixes no topology. Consumers must bind
the actual rational-point topology `rationalPointTopology` of
`AlgebraicGeometry.PointTopology.RationalPoints`;
local compactness, the nonarchimedean group property and radical closedness
remain required for the normalized functors.
The standard simple-root/cocharacter family and Coxeter comparisons are still
needed; the dynamic bridge does not identify an arbitrary cocharacter family
with the required standard family.

The same version adds `jacquetFunctor_preservesShortExact`, assuming the
actual radical is a limit of compact subgroups, and
`normalizedInductionFunctor_preservesShortExact`, assuming a Hausdorff group,
compact-open cofinality, a closed parabolic and continuous projection.
`ParabolicFiniteLength.of_preservesFiniteLength` then assembles the existing
predicate from those inputs and the two finite-length-preservation premises.
Their structural specialization is not automatic. A compatibility check
compiled the six main/geometric target modules against the same Parabolic and
AlternatingOperator files, with no diagnostics and the same geometric-target
fingerprints; it is not a proof of any target.

## Check evidence

The five main pairs (contragredient, induction, Jacquet, involutivity and
cuspidal eigenvalue), the geometric pair, the Corollary pair and the
Weyl-conjugacy pair are in the Library as target modules
(`Aubert.General.ContragredientTarget`, `InductionTarget`, `JacquetTarget`,
`InvolutivityTarget`, `CuspidalEigenvalueTarget`, `GeometricK0Target`,
`Aubert.GeneralCorollaryTargets`, `Aubert.GeneralWeylConjugacyTarget`). A
development check compiled the geometric pair with zero errors/warnings and
inspected `GeometricK0ExpansionStatement` as returning `Prop` with the
standard axioms; it is not a proof, and the Library has no proof of this generic statement; on the actual rational-point families it proves the expansion under the displayed premises (`RationalPointFamily.rationalGeometricK0Expansion`, module `RationalGeometricK0Expansion`). The
Weyl-conjugacy pair corrects the representation-carrier/K0-type universe
distinction without changing either Lean proposition. Being in the Library
does not make these targets proofs.

## Original-source and reading record

| Registered original | SHA256 | Extent supporting this table |
| --- | --- | --- |
| `aubert-1995-duality` | `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693` | Printed pp.2179–2183 were read directly, including the five identities, (1.3), cuspidality and Corollary 1.10; p.2183 was checked visually for its signs and inverse conjugation. |
| `renard-2026-representations-groupes-reductifs-padiques` | `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c` | The finite/subgroup companion records direct reading of V.3.6–13 and V.4.1–6; this table retains its full-centralizer, central-direction and realization distinctions. The adapter companions identify the VI.1 and VI.6 representation prerequisites. |
| `ban-jantzen-2016-duality` | `7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4` | Proposition 4.1 and its proof, printed p.158 / PDF p.6, were read directly, confirming the three proof ingredients. The Corollary pair records the corresponding target/source audit. No new finite-central-extension theorem is claimed. |
| `casselman-1995-admissible-representations` | `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a` | Printed/PDF pp.2 and 67–68 were read directly, including the admissible setting, Lemma 7.1.1, Corollary 7.1.2 and Theorem 7.1.4. The Corollary companion records the intended general deductions. No omitted applicability proof is supplied by citing these pages. |

The corrected irreducibility argument and erratum boundary remain those in
the general program source map. Aubert Proposition 3.2 supplies no evidence
for any construction, target or future proof listed here.
