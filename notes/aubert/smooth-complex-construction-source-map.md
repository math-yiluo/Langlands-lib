# General Aubert smooth complex: constructions, targets and dependencies

Workers 194 and 379, task `0a1bd7fb-66c2-4dcc-a3c8-6619f6fa10b4`,
revision 1, 3 November 2026. This note maps the normalized smooth complex,
its terminal cokernel and the corrected exactness, support, graded-filtration,
Jacquet-comparison and finite-length/irreducible consequence targets to
their sources, declarations and remaining proof obligations.
It distinguishes the reusable subgroup-family construction from the
literal rational-point specialization; exact publication status is given
below.

This note supplements
[the general source map](general-program-source-map.md) and
[the common Chapter V ledger](../renard/chapter-v-structural-inputs.md).
It covers the actual smooth complex, the corrected full-smooth exactness
and terminal-Jacquet targets, and Worker 379's actual support, filtration
and finite-length/irreducible consequence specializations. Their
[detailed companion source map](support-filtration-consequences-source-map.md)
records the reusable generic layer and source reading.
That companion note, candidate
`1a4ffc2e-66e8-4163-9d01-693897006cfb`, is independently accepted and public
at commit `db075b95ca445b245271537742cad6a6d876df15`.
Parent Worker 76 retains focused proof successors,
the final dependency matrix and proof closure.

The reusable constructions use subgroup families with explicit
decomposition, closedness, normalization and nesting laws. Their proposition
targets may fail for arbitrary families of that shape. The rational-point
specializations below instead fix the actual standard groups and topology
for general connected reductive groups, retaining nonsplit and
nonquasisplit groups, permitted positive characteristic and relative rank
zero. Their named structural and topological inputs remain explicit.
Publishing faithful targets does not prove them.

## Conventions and actual maps

Let `S` be the finite ordered simple relative-root index. A standard family
has increasing `P(J)` and decreasing `U(J)`, with actual semidirect
decompositions `P(J) = M(J) U(J)`. The construction uses the removed subset
`s = S \ J`. Thus degree `k` means `|s| = k`. The terminal degree for support
type `{I}` is `|S| - |I|`, whose coordinates are exactly the surviving
subsets `J` with `|J| = |I|`. The original `I` is passed unchanged to the
cokernel construction.

Each coordinate is the genuine normalized functor object `i_J(r_J(E))`.
Its carrier consists of smooth induced functions valued in the actual
`U(J)`-coinvariants. Worker 23's normalization comparison with
`SubgroupTransition.term` preserves those functions. Transporting the
canonical quotient transition through this comparison therefore sends a
function `f` to the function whose value at `g` is the class of `f(g)` in
the larger-radical quotient. Its identity, composition, equivariance and
ambient-morphism naturality laws are proved, rather than supplied as
arbitrary complex data.

The increasing cut basis represents the exterior orientation line in
Aubert 1995, p.2187. The implementation uses left insertion, whereas Aubert
appends on the right. The existing `CutSignReorientation` comparison gives
the degreewise factor `(-1)^(k.choose 2)`, intertwines the actual
differentials and identifies their kernels and incoming images. The signed
sum of the transitions gives the differential. Diagram composition proves
square zero with the same signs.
The natural normalization comparison intertwines the signed differentials,
so objectwise comparison alone is not the claimed implementation.

The incoming submodule is zero in degree zero and the image of the
preceding differential in positive degree. Equivariance makes it invariant.
The terminal object is its actual smooth quotient, with the descended
action and canonical surjective projection. The projection's kernel is
exactly the incoming submodule. These quotient laws do not assert
exactness in earlier degrees.

## Reusable subgroup-family declaration map

All namespaces in the next table begin with
`Langlands.Aubert.General`. All module paths begin with
`Langlands/Representation/Aubert/General/`. All nine pairs in this table
are independently accepted and public at this snapshot.

| Pair | Exact declarations and content | Provenance and remaining boundary |
| --- | --- | --- |
| `Complex` | `Complex.termObject_eq`, `transition`, `transition_eval`, `diagram`, `diagramEquivalence`, `differential`, `differential_square`, `degreeObject`, `degreeEquiv_differential` | Intrinsic assembly of actual functors, quotient transitions and published signed-diagram laws. General standard-root realization remains separate. |
| `Terminal` | `Complex.boundary`, `terminalProjection`, `terminalProjection_surjective`, `terminalProjection_ker`, `terminalObject`, `terminalDegree`, `sharpObject`, `terminalEquiv_projection` | Actual invariant-image quotient and comparison with the same unnormalized subgroup-family complex. This comparison is not the associated-Levi assertion. |
| `Naturality` | `Complex.termMap`, `termMap_natural`, `degreeFunctor`, `terminalMap`, `terminalMap_comp_projection`, `terminalFunctor`, `sharpFunctor`, `differentialNat`, `terminalProjectionNat` | Actual functor maps and quotient universal properties prove naturality on all smooth intertwiners. |
| `Initial` | `Complex.augmentation_eval`, `transition_augmentation`, `initialMap`, `initialEquiv`, `initialMap_natural`, `initialDifferential_square` | Orbit functions give the first map. The equivalence uses `P(∅)=G`, `U(∅)=1` in removed-subset notation. |
| `StandardComplex` | `StandardComplex.removedFamily`, `terminalIndexEquiv`, `termObject_eq`, `sharpObject`, `sharpFunctor`, `initialEquiv` | Complement dictionary, including cardinalities, signs and canonical maps. Standard endpoints are `P(S)=G`, `U(S)=1`. |
| `StandardExactness` | `StandardComplex.IsExactBeforeTerminal`, `terminalProjection_surjective`, `terminalProjection_ker`, `initialDifferential_injective_of_exact`, `isExactBeforeTerminal_univ` | Defines the truncation convention and proves intrinsic implications. It does not prove corrected Theorem 3.6. |
| `CorrectedTheorem36` | `CorrectedTheorem36Statement` | Source target: every smooth object of `Alg({I})` is exact before terminal degree. No finite-length, admissibility or irreducibility premise. |
| `LeviComplex` | `LeviComplex.family`, `family_monotone`, `family_antitone`, `sharpFunctor`, `sharpObject` | Actual subgroup intersections inside a closed `M(J)` and the same complex construction, indexed by subsets of `J`. |
| `TerminalJacquet` | `TerminalJacquet.supportObjects`, `JacquetCuspidalStatement`, `FixedLeviComparisonStatement`, `AssociatedLeviComparisonStatement` | Full-smooth support subcategory, separate cuspidality prerequisite and natural-isomorphism versions of the p.4690 comparisons. Worker 165 contributed the elementary conjugate-subgroup membership proof. |

`CorrectedTheorem36Statement` requires `ker(d_k)` to equal the actual
incoming image for `k < |S|-|I|`. Its endpoint parameters identify degree
zero with `E`. At positive terminal degree, this implies injectivity of
the canonical first arrow. At terminal degree the actual quotient
projection has its proved kernel and surjectivity laws. There is no
condition on an outgoing differential there and no final zero killing
`E#`. For `I=S`, including `S=∅`, the earlier-degree predicate is vacuous
and the degree-zero quotient is retained.

`TerminalJacquet.FixedLeviComparisonStatement` requires
`Sharp_(M(I))(univ) ∘ r_I ≅ r_I`.
`AssociatedLeviComparisonStatement` requires
`r_I ∘ Sharp_G(I) ≅ Ad(n) ∘ Sharp_(M(I'))(univ) ∘ r_(I')`.
Here `I'` is `RelativeWeylIndexing.associatedSubset actual I`, and `n`
ranges over every lift of `RelativeWeylIndexing.longestRep actual I` in
the actual normalizer quotient. The named structural prerequisite
`actualAssociatedLeviConjugation` identifies the actual Levis.
Conjugation acts by `x ↦ σ(n⁻¹ x n)`. Both sides are actual functors on
the full smooth support subcategory; `Nonempty` requires a complete
natural isomorphism. This strengthens the displayed source object
comparison to compatibility with every equivariant map. No comparison
proof is supplied.

## Actual rational-point constructions and targets

The generic subgroup-family declarations above remain reusable constructions
and intermediate targets. Their general representation-theoretic conclusions
need not hold for arbitrary families satisfying only their displayed
construction laws. The following specializations instead fix the actual
rational-point group, topology, standard subgroups and root association.
They supply faithful targets for the general reductive proof successors;
they do not prove those targets.

All declarations in this subsection have namespace
`Langlands.Aubert.General.RationalPointFamily`. Their module prefix is
`Langlands.Representation.Aubert.General`.

| Pair | Exact declarations | Meaning and source |
| --- | --- | --- |
| `RationalStandardComplex` | `standardParabolic_monotone`, `standardUnipotent_antitone`, `standardParabolic_univ`, `standardUnipotent_univ`, `rootAssociation` | Evaluate the named all-test standard-family assertions at actual root subsets and the identity test object. Association uses an actual torus-normalizing representative and the actual normalizer/full-centralizer character action. |
| `RationalStandardComplex` | `rationalDegreeObject`, `rationalDifferential`, `rationalBoundary`, `rationalTerminalProjection`, `rationalSharpObject`, `rationalSharpFunctor`, `rationalInitialMap`, `rationalInitialEquiv`, `rationalInitialDifferential` | Substitute the literal rational-point families and derived decomposition, order and normalization laws into the canonical normalized complex. Aubert 1995 pp.2186–2187; erratum p.4687 (*) and p.4690. |
| `RationalCorrectedTheorem36` | `RationalCorrectedTheorem36Statement` | The corrected exactness target for every smooth object in the actual `Alg({I})`, with no finite-length premise and with the terminal cokernel retained. Erratum p.4687 (*). |
| `RationalCorrectedTheorem36` | `rationalTerminalProjection_surjective`, `rationalTerminalProjection_ker` | Proved intrinsic quotient laws on the same actual construction. They require neither the exactness target nor membership in the support category. |
| `RationalTerminalJacquet` | `standardLeviUnipotent_isUnimodular` | Derive the modulus prerequisite for each restricted radical inside a closed actual Levi from its separately stated compact-limit property. |
| `RationalTerminalJacquet` | `RationalJacquetCuspidalStatement`, `RationalFixedLeviComparisonStatement`, `RationalAssociatedLeviComparisonStatement` | Separate full-smooth support/cuspidality and natural-comparison targets. The last two give the natural-isomorphism versions of the equality preceding (**) and display (**) in erratum p.4690, Remark (1). |

The group is literally `RationalPoint k G.X`, with
`RationalPointFamily.pointTopology`, the canonical evaluation topology.
The statement wrappers quantify over a nonarchimedean local field, a connected
reductive group scheme, a maximal split torus `i` and a generic cocharacter `ν`.
They retain nonsplit and nonquasisplit groups, permitted positive
characteristic and the empty simple-root set. They derive the finite
enumeration of `SimpleRoot i ν` from `HasRelativeRootSystem` and the splitness
of the torus, then quantify every linear order for the exterior coordinates.
No splitness of the ambient group follows from this enumeration.
The smooth representation carrier universe is `max (u+1) v`.

The families are exactly `parabolic i ν`, `levi i ν` and `unipotent i ν`,
evaluated on `rootSet i ν I`. The structural hypotheses are named propositions,
not freely supplied subgroup decompositions, nesting fields or arbitrary
normalizations. The adapters derive ambient and inside-Levi decompositions.
They derive radical unimodularity from compact-limit assertions and reuse the
actual positive induction and inverse Jacquet half-characters. The source
comparison of induction with the inflated Levi half-character uses this
unimodularity. A root-product formula for the modulus is not proved here.

`rootAssociation i ν hN hZ I J n` requires the same ambient point `n` to
normalize the image of the torus points and its quotient class to carry
exactly `rootSet i ν I` to `rootSet i ν J`. The normalizer and centralizer
point comparisons preserve the representative; the denominator is the full
centralizer. `IsInSupportCategory` separately requires that this same `n`
conjugate the actual Levis. It then tests every irreducible subquotient against
actual normalized induction of an irreducible cuspidal Levi representation.
This is the full smooth support category of erratum p.4687, not a
finite-length subcategory.

The differential, initial map and terminal projection are literal
specializations of the canonical maps described above. Naturality and square
zero are inherited from the published implementation, rather than asserted
for arbitrarily chosen maps between isomorphic objects. The exterior
left/right insertion comparison remains the degree factor
`(-1)^(k.choose 2)`. The retained quotient is at removed-root degree
`|S|-|I|`; its coordinates have `|J|=|I|`. In degree zero the incoming
boundary is zero. In particular, `I=S` and relative rank zero retain the
initial object rather than assert its vanishing.

The associated-Levi target additionally fixes a Coxeter system on the actual
simple-root subtype and actual normalizer/full-centralizer quotient. Its
named root, Levi-Weyl and minimality comparisons identify
`I' = associatedSubset actual I` with the actual character image `w_I⁻¹(I)`.
For every normalizer lift `n` of the specified longest representative it asks
for

`r_I ∘ Sharp_G(I) ≅ Ad(n) ∘ Sharp_(M(I'))(univ) ∘ r_(I')`.

Conjugation acts by `x ↦ σ(n⁻¹ x n)`. Both sides use actual normalized
Jacquet and retained-cokernel functors on the full support subcategory.
`Nonempty` requires an entire natural isomorphism, including inverses and
compatibility with every equivariant map. This is the disclosed functorial
strengthening of the source's displayed object comparison.

### Actual support, graded-filtration and consequence targets

Worker 379's three actual-point modules specialize the published generic
targets; they assume no instance of those targets. Their common field,
group, topology, standard families and carrier universe are exactly those
described above. Each declaration is a `Prop`-valued definition, and its
publication status is recorded separately below. The companion
[support/filtration source map](support-filtration-consequences-source-map.md)
gives the generic definitions and detailed source reading; this section
records their actual rational-point specializations.

All names in the next three tables have namespace
`Langlands.Aubert.General.RationalPointFamily`.

| Declaration in `RationalSupportCategoryTargets` | Actual assertion | Source locator |
| --- | --- | --- |
| `RationalCuspidalSeriesExistenceStatement` | Every irreducible smooth representation belongs to some actual cuspidal series. | Renard, Corollaire VI.2.1, p.139. |
| `RationalCuspidalSupportAssociationStatement` | Two actual cuspidal inducing data with a common irreducible subquotient are associated, including the conjugation isomorphism of the inducing representations. | Renard, Théorème VI.5.4 (iv) ⇒ (i), pp.173–174. |
| `RationalSupportCategoryAssociationInvarianceStatement` | The full smooth support category depends only on the association class of the standard Levi. | Erratum p.4687, definition of `Alg({I})`. |
| `RationalSupportCategoryIrreducibleJacquetDetectionStatement` | An irreducible member has a nonzero Jacquet module along some associated standard Levi. | Proof of Renard VI.5.4, pp.173–174. |
| `RationalSupportCategoryZeroDetectionStatement` | If all associated standard-Levi Jacquet modules of a member vanish, the member is zero. | Erratum p.4687, first sentence of the proof. |
| `RationalSupportCategoryExactnessDetectionStatement` | Exactness at a middle object in `Alg({I})` is equivalent to exactness after every associated standard-Levi Jacquet functor, using the actual maps. | Same erratum sentence. |
| `RationalSupportCategoryInductionJacquetStatement` | Every actual `i_K r_K` preserves the full smooth support category. | Renard VI.7.2, p.182, and VI.7.3, p.185. |
| `RationalSupportCategoryJacquetVanishingStatement` | The actual `r_K` vanishes if `L_K` contains no standard Levi associated to `L_I`. | Renard VI.5.3(i), p.173, and VI.7.3. |
| `RationalSupportCategoryDecompositionStatement` | Every smooth representation is an internal direct sum of subrepresentations in these support categories; summands may be zero and uniqueness is not asserted. | Renard VI.7.2, p.182, grouped by association class. |

Association always includes both `rootAssociation` and conjugation of the
actual Levis by the same representative. Irreducible detection asserts
nonvanishing for some associated Levi; zero and exactness detection test
all associated Levis. The published
`supportCategoryZeroDetection_of_irreducibleJacquetDetection` is a
conditional generic reduction, not a proof of the actual irreducible
detection target. Its nonzero irreducible-subquotient input has full smooth
scope, as in Renard III.1.4, p.60.

| Declaration in `RationalCorrectedFiltrationTargets` | Actual assertion | Source locator |
| --- | --- | --- |
| `RationalCorrectedGradedVanishingStatement` | A nonzero grade of `r_I(E_J)` at a length-ordered actual Weyl element `w` forces, for every normalizer lift `m` of `w⁻¹`, a standard `K ⊆ J` with `L_K = m⁻¹ L_I m`. | Erratum pp.4688–4689; Ban–Jantzen §4, pp.160–162. |
| `RationalCorrectedGradedTransitionStatement` | On all surviving grades simultaneously, surjections from step `i+1` to `Ad(w⁻¹)(r_K E)` have kernel step `i` and intertwine the actual Jacquet transitions with identity maps. | Erratum pp.4688–4690; Ban–Jantzen p.162. |

These use `T := torusPoints i` and the actual quotient
`Weyl i = N_G(T)/Z_G(T)`, with the full centralizer as denominator. Both
quantify an explicit finite enumeration of this Weyl group and every
Coxeter system on it indexed by the actual simple roots. The premises
`RootLengthComparison`, `PositiveSimpleReflectionComparison` and
`actualLeviWeylIdentification` tie its length, simple reflections and
standard Coxeter subgroups to the actual character action and Levi Weyl
images. They are distinct intermediate obligations.

A surviving coordinate has `J = S \ s`, `K ⊆ J` and `w` minimal in
`W_J w W_I`. The transition target chooses its quotient maps together and
requires their commuting squares for all surviving `s ⊆ t`. The
unsigned transitions become identities; the assembled differential keeps
the exterior signs. The reused two-sided support and length-order
minimality lemmas remain finite Weyl lemmas until these actual
representation-theoretic comparisons are proved. This filtration places
no composition-length restriction on `E`.

| Declaration in `RationalSharpConsequenceTargets` | Actual assertion | Source locator |
| --- | --- | --- |
| `RationalSharpFiniteLengthStatement` | Finite length of `E` implies finite length of its actual terminal cokernel `E#`. | Prerequisite for Corollary 3.9(a); Renard VI.6.2, p.178, and VI.6.4, p.179. |
| `RationalSharpClassFormulaStatement` | For finite-length `E ∈ Alg({I})` with `E#` finite length, `D_G[E] = (-1)^|I| [E#]` in the exact finite-length Grothendieck group. | Aubert 1995 p.2189, Corollary 3.9(a), extended to `Alg({I})`; erratum p.4690. |
| `RationalSharpSupportRetentionStatement` | `E ∈ Alg({I})` implies `E# ∈ Alg({I})`. | Derived iteration prerequisite, erratum pp.4687 and 4690. |
| `RationalSharpIrreducibleStatement` | `E ∈ 𝔈(I)` implies that `E#` is nonzero and irreducible. | Aubert 1995 p.2189, Corollary 3.9(b). |
| `RationalSharpCuspidalSeriesStatement` | `E ∈ 𝔈(I)` implies `E# ∈ 𝔈(I')` for some associated actual standard Levi, with root association and same-representative Levi conjugation. | Derived prerequisite in the proof of Corollary 3.9(c), p.2189. |
| `RationalSharpInvolutionStatement` | `E ∈ 𝔈(I)` implies an actual smooth representation isomorphism `(E#)# ≅ E`, with both cokernels at degree `|S|-|I|`. | Corollary 3.9(c), p.2189. |

Here `IsInCuspidalSeries` includes irreducibility of `E`. The actual
`E#` is the same `rationalSharpObject` as above. The class-formula target
quantifies `hfl : ∀ J, ParabolicFiniteLength …` internally, as the proof
parameter used to define the alternating operator; it does not prove that
parameter. It separately assumes finite length of `E#`, whose proof is
the first target. The support and involution targets are object-level
assertions; a Grothendieck-class equation alone supplies no arbitrary
representation isomorphism.

Termwise exactness and finite length have separate published interfaces.
In namespace `Langlands.Aubert.General`,
`jacquetFunctor_map_isShortExact` and
`normalizedInductionFunctor_map_isShortExact` prove preservation
of all smooth short exact sequences under their displayed topological
hypotheses. Applying them to these actual families still requires compact
limits for the radicals and, for induction, closed parabolics and
continuity of the actual semidirect projection. The actual-family adapter
`RationalPointFamily.standardParabolicFiniteLength` combines those
exactness results with separate finite-length preservation premises
`hiFl`, `hrFl`; it does not prove those premises.
`DynamicInductionFiniteLengthStatement` and
`DynamicJacquetFiniteLengthStatement` in
`PrerequisiteStatements` are actual dynamic-group targets for Renard
VI.6.2 and VI.6.4, with `rational_parabolicFiniteLength` as their
conditional exactness bridge. Comparison with the standard families
must use the named structural adapters. These functor and finite-length
interfaces remain with sibling
`593ef603-6672-4424-976c-14e11e920d9c`; the parent's proof successors
retain support decomposition, extension, the Euler argument and the
Corollary 3.9 proofs. None is a field in the complex construction.

The precise extra premises of these three modules vary by declaration.
All retain the common actual setting, `hStandard`, `hRoots` and radical
closedness `hU`. The following table lists the further premises; none of
these 17 declarations uses `hEndpoints`.

| Declarations | Further premises |
| --- | --- |
| All nine support targets | `hInter`, Levi closedness `hM`; all except `RationalCuspidalSeriesExistenceStatement` also use `hN`, `hZ`. No `hOrder`, `hUc` or exterior linear order. |
| Both graded targets | `hInter`, `hM`, `hN`, `hZ`, a linear order on actual simple roots, finite actual Weyl group, actual Coxeter system and the three comparisons above. |
| Graded-transition target only | In addition, `hOrder` and ambient compact limits `hUc`, supplying the canonical transition maps and their normalization. |
| All six sharp targets | `hOrder`, `hUc` and a linear order on actual simple roots. All except `RationalSharpFiniteLengthStatement` also use `hInter`, `hM`. |
| Sharp class formula, support retention and cuspidal-series targets | In addition, `hN`, `hZ` for actual root association. |

The ambient and inside-Levi decompositions, nesting and unimodularity are
derived by the same published adapters as above. These are derived
specializations of the generic propositions, not newly assumed
representation theorems. Their structural, root, closedness and topology
premises must be discharged or matched to the parent's itemized external
structural ledger. Their support, graded-map, finite-length,
irreducibility and involution conclusions remain representation-theoretic
proof obligations.

## Verified published construction inputs

TaskHub fetches verified acceptance and publication of the following
candidates. The normalized core's acceptance covers its intrinsic
constructions; it does not accept the remaining proposition targets.

| Candidate | Published module and reusable content |
| --- | --- |
| `8e4ecc04-eb7d-4d85-aefa-fc08adc02b55` | `Langlands.Representation.Jacquet.LocalizationTransition`: canonical quotient maps, composition, surjectivity and naturality. |
| `5a739fef-b96d-47fa-883f-7e8ccfd0ec01` | `Langlands.Representation.Aubert.SubgroupTransition`: actual induced-function term, quotient transition and orbit augmentation. |
| `744910e0-e746-42b2-8752-fa1533d22e91` | `Langlands.Representation.Aubert.SubgroupComplex`: signed diagram, differential, square zero, smooth homogeneous objects and invariant-image quotient. |
| `36a3b4fa-ada2-4e59-8827-b9201d102e24` | `Langlands.Representation.Aubert.SubgroupComplexNaturality`: actual degree and terminal maps, their chain-map law and functor laws. |
| `69e34908-3a42-4bd9-8277-76f51f403f40` | `Langlands.Representation.Aubert.SubgroupInitialTerm`: `SubgroupTransition.initialEquiv`, the canonical full-group/trivial-radical orbit-function equivalence. |
| `2307c53c-99f4-465f-868d-693b7da8f731` | The five `General` pairs `Complex`, `Terminal`, `Naturality`, `Initial`, `StandardComplex`: actual normalized diagram and smooth quotient functor, with canonical map laws and the complement dictionary. |

The first three candidates were published at commit
`47cd8b71e79c9bb4aba6d9cc2664cb09fbff441c`; the fourth and fifth at
`11dedf3c6982c420e1eee5dc7a82ee37ad2dcc0e`.
The normalized core is public in
`7543113c99690e18b45f3b22d252e8cf77c3964e`.
The exactness pair and corrected Theorem 3.6 target are independently accepted
and public as `8e0a52c1-cdb7-4903-9093-583311f03500`, first checked in
`d3ab507f01d1e2e025d7fd38df0d2b7f78a9e301`.
The Levi-complex and terminal-Jacquet pairs are independently accepted and
public as `91651bfd-0a54-443a-aac7-da6107baf75d`.
All eighteen files of these nine pairs were compared with Library
`1271a6b7c9a470deaa1b8e2aadc2e2defd10f5b5` and agree.
The restoration Lean check of all nine modules reported zero errors and
warnings and confirmed that `AssociatedLeviComparisonStatement` returns
`Prop`. This development check is separate from independent acceptance.
Current mathematics is located by Lean name, not by submission identity.
Worker 379's independently published `RankOrderedSupports` supplies
`Support.modifiedRankSupport_succ_diff` and
`Support.modifiedRankSupport_succ_minimal`; these are finite group/rank
lemmas, not a proved actual Bruhat or geometric-lemma comparison.
Worker 379's `CorrectedFiltration` construction is independently accepted and public
as `1c48a424-f7e9-4aec-b326-4d81e098fbf0` at
`d3ab507f01d1e2e025d7fd38df0d2b7f78a9e301`, and both workspace files
agree with the public tree. The six consequence targets in
`SharpConsequenceStatements` are independently accepted and public as
`6da10c90-35c3-45d0-a60b-cc0ee8169807`; both files agree with Library
`1271a6b7c9a470deaa1b8e2aadc2e2defd10f5b5`.
The graded targets `CorrectedGradedVanishingTarget` and
`CorrectedGradedTransitionTarget` in `CorrectedFiltrationStatements`,
candidate `bd7db6bd-c5d0-4a71-bdc3-dbd14b3f789b`, are independently
accepted and public at commit `5d3754ec863f6d5013aca65cbcec0801e6972d1f`.
They require the surviving
grades and their actual transitions to be identified together, not by
unrelated objectwise isomorphisms. The companion note gives their exact types.

Worker 23's corrected adapter candidate
`434a4095-6e40-4821-becc-73e6edef6124` is independently accepted and public,
verified by a fresh TaskHub fetch against Library
`7a2e42fd31831029d34cafb155ffad911920df25`. Its
`Parabolic` pair corrects the source identification: generic induction
twists by the half modulus on all of `P`; agreement with the source's
inflated Levi half modulus requires `IsUnimodularModulus U hU`.
Jacquet restriction agrees with BZ `r_{U,1}` and Renard for every supplied decomposition. Induction agrees with BZ `I_{U,1}` under the unimodularity premise, by `closedHalfCharacter_eq_comp_projection`. The comparison used here carries that premise. Compact containment can
prove this unimodularity; it is retained proof work, not a new external
structural assertion. The rejected predecessor
`214d3c61-c6e3-4576-b94e-57c72d2e7e55` is not dependency evidence.

### Actual rational-point publication status

The construction pair `RationalStandardComplex`, candidate
`b6f76d1b-00b2-4051-9a68-44378a9c91a4`, is independently accepted and public
at exact commit `223b9c65844ea8eecb00eafaad77269b9b54d787`.
Its two files were read from that exact public commit and their SHA-256
fingerprints agree with the submitted and current workspace files:
Lean `f32429dea0b5e5fdd23aedd1962edf38db25b8d1d8c2c568e8786192c4c768c5`,
Markdown `819e372db40030a2a2678eec028d3c058e13fc35c91adf2cefbd4b08b305877d`.

The actual exactness target `RationalCorrectedTheorem36`, candidate
`fc768c49-1370-4f2b-8737-b722256f3d67`, and the terminal-Jacquet targets
`RationalTerminalJacquet`, candidate
`e1f169d2-3306-4973-9847-f8a0a11ffb6b`, are independently accepted and public
at exact commit `405ff58c5df69766419c9941161444531c1979ae`.
The two primary Lean/Markdown pairs and the unchanged construction pair
carried by both bundles were checked byte-for-byte against that Library
commit and the submitted files. Their independent reviewers were
Reviewer 9861 and Reviewer 9946, respectively; neither review has unresolved
qualifications.

Worker 379's following actual-point target candidates are independently
accepted and public at exact commit
`6820dc99b5972ed5761be21b4ac8afeba7584644`. Each has accepted machine
validation and an independent approving review without review qualifications:

| Candidate | Module | Independent reviewer |
| --- | --- | --- |
| `61257d3f-bcc6-4005-8eb4-0003392332ab` | `RationalSupportCategoryTargets` | Reviewer 10117 |
| `ba8ecb0f-f16a-4ae6-a48a-8cbdc129d8ba` | `RationalCorrectedFiltrationTargets` | Reviewer 10140 |
| `91d2f55a-8079-4b52-b9e4-17f41ca090c3` | `RationalSharpConsequenceTargets` | Reviewer 10147 |

Their six Lean/Markdown files were checked byte-for-byte against the exact
Library commit, accepted archives and frozen bundle fingerprints. Their
declaration descriptions above follow those exact pairs. The joint
source-map check by Worker 379 is coauthor input and does not replace
independent review of this note.

The restoration check `994acef2-bf6e-45cf-a5d8-3a712e144acd` compiled all
three Worker 194 rational-point modules with zero errors and warnings and
inspected `RationalAssociatedLeviComparisonStatement` as Prop-valued. This development
check is separate from semantic acceptance and publication, and proves none
of the representation-theoretic targets.

## Source passages and repaired proof obligations

| Source locator | Construction or target | Obligation still required for a proof |
| --- | --- | --- |
| Aubert 1995, pp.2186–2187, transition law (3.1) and complex (3.5) | Actual normalized terms, canonical quotient maps, orientation signs and square zero | No appeal to Proposition 3.2. The intrinsic map laws are implemented directly. |
| Erratum p.4687, `Alg({I})` and display (*) | Full-smooth support predicate and corrected truncation | Support detection after actual Jacquet restriction, full-smooth termwise exactness and the corrected filtered comparison. Induction on composition length alone cannot prove the unrestricted target. |
| Ban–Jantzen §4, pp.161–162 | Two-sided modified supports and signed graded maps | For each target/source pair use `θ^{J,I}={x∈θ : W_J x W_I⊆θ}`. Compare consecutive modified supports and prove double-coset minimality before the geometric lemma. Remaining elements have length at least that of the removed element. |
| Ban–Jantzen p.162, integral comparison | Canonical surviving-grade transition squares | Prove equality of the integration subgroups and composition of actual quotient maps, obtaining identity maps up to exterior signs. Isomorphism of coordinate objects is insufficient. |
| Erratum p.4690, Remark (1), display (**) | Retained cokernel and associated-Levi comparison | Prove the actual graded comparison, its naturality and the surviving terminal grade; keep the associated-Levi conjugation and all normalization maps. |
| Aubert 1995, Corollary 3.9, p.2189; erratum p.4690 | Worker 379's finite-length and irreducible consequence targets | Prove finite length of `E#`, exact-class Euler formula, extension, support retention, nonzero irreducibility and actual biduality. The class identity alone gives no arbitrary module isomorphism. |

The erratum explicitly withdraws the proof of Proposition 3.2 and leaves
the proposition unresolved. Its false homogeneous-space identification
on Aubert 1995 p.2187 does not disprove the proposition. The original
p.2188 proof of Theorem 3.6 uses it and is not evidence. The erratum's
left-saturated supports on pp.4687–4689 must be replaced by the two-sided
supports above. Read Ban–Jantzen p.161's parenthesis as comparing
`θ_i'` and `θ_(i+1)'`. Do not use the literal p.160 claim that the whole
complex ending in zero is exact: terminal homology must survive.

The finite Weyl filtration bounds the number of support steps. It says
nothing about the composition length of an arbitrary smooth `E`.
Boolean contraction and finite-filtration lifting must be applied to the
actual graded diagrams with their proved transition maps. Generic Boolean
lemmas do not supply the geometric lemma, cuspidal support or its detection.

## Structural realization and proof ownership

The table records the exact consumer inputs and the shared source and owner
boundaries. Its references to S/D rows use the common Chapter V ledger.
A named all-test statement is an intermediate hypothesis until its exact
required clause has a proof or is matched to the parent's itemized external
structural list. An implementation comparison and an in-book deduction do
not become external assumptions by appearing in such a statement.

| Input or adapter | Source boundary | Proof and ownership boundary |
| --- | --- | --- |
| `StandardCocharacterStatement`; `isSemidirectDecomposition_of_standardCocharacterStatement` | S06, S10, S15: Renard V.3.1, V.3.8–V.3.9 and V.4.2 | The published adapter derives the actual decomposition from the named statement and the dynamic decomposition theorem. The named general statement remains a prerequisite of standard-parabolic owner `8ace819d-9522-4381-aaab-f9a84a07755e` in algebraic-groups program `2b5e4a00-9d44-49a4-9c89-979fb5b6233e`. |
| `StandardParabolicOrderStatement`, `StandardParabolicEndpointsStatement`; the four `standard*` evaluations above | S15: Renard V.4.2, p.118 | Pointwise evaluation and root-subset conversion are proved; the universal structural statements are not proved by these evaluations. Same standard-parabolic owner. |
| `StandardLeviIntersectionStatement`; `isSemidirectDecomposition_in_levi` | S11: Renard V.3.10–V.3.11, p.112 | The actual subgroup intersections and their conditional decomposition adapter are implemented. The named all-test structural assertion remains separate with the same owner. |
| `HasRelativeRootSystem`, `simpleRelativeRootFintype`, `HasPointNormalizerComparison`, `HasPointCentralizerComparison`, `weylCharacterAction` | S05, S08–S09, S12; retained D01/D04 comparisons | The actual character action and finite-enumeration adapters are implemented under the displayed premises. Their mathematical structural inputs and exact scheme/point comparison bridges remain distinct. Structural lead: `6edfb074-480e-4f66-ba8f-dbf5d7a54a5a`; relative-Weyl consumer: `e3d69272-2599-4a08-a934-cb11f2493e30`. |
| `RootLengthComparison`, `PositiveSimpleReflectionComparison`, `actualLeviWeylIdentification`, `minimalityLengthCriterion`, `associatedSubsetLaws` | S09, S13, S17–S18; retained D06 | The associated target keeps all five separately. The root-sign/Coxeter realization is not supplied by an arbitrary finite Coxeter group. The in-book conversions and associated-subset deductions retain proof obligations; parent Worker 76 coordinates their exact proof successors with the relative-Weyl and structural owners. |
| `actualAssociatedLeviConjugation` | D06: Renard V.4.3–V.4.8 | Public `associatedLeviConjugation_of_standard` in `RationalAssociatedLeviConjugation` supplies this precise premise from `GroupScheme.StandardLeviConjugationStatement` and the same actual root comparisons. It proves the conditional adapter for every lift, not the general structural statement or the representation comparison. The approved target retains the premise explicitly. |
| `pointTopology`; local compactness, nonarchimedean group structure and Hausdorffness; closed actual radicals and Levis | S01, S04; implementation comparisons | These properties are requested on the pinned topology. Available affine point-topology results must be applied with their actual hypotheses and subgroup comparison maps. Conrad owner `886bf565-95e9-4dc6-8a9d-73284a523668` supplies the topology realization; the standard-subgroup bridges remain explicit. |
| Ambient `hUc` and inside-Levi `hUcLevi` compact-limit assertions | S22: Renard V.5.2(iii), p.123 | The wrappers retain both assertions separately. Ambient containment does not by itself discharge the restricted premise. KP program `f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703` and the existing dynamic compact-containment owner supply the structural route. `standardUnipotent_isUnimodular` and `standardLeviUnipotent_isUnimodular` prove the normalization consequences; the latter pulls closedness back along the Levi inclusion. |
| Source modulus/root-product comparisons | D07: Renard V.5.4, pp.126–127 | Intrinsic Haar characters and the unimodularity adapters define and compare the functors used here. The remaining general reductive root-product and quotient-modulus formulas are in-book proofs, not additional external fields. |
| Full-smooth exactness, support detection, geometric-lemma and canonical graded-map comparisons | Erratum pp.4687–4690; Ban–Jantzen §4 pp.160–162 | Representation-theoretic obligations remain outside S01–S23. Worker 379 supplies the actual support, filtration and consequence targets and companion source map; Worker 76 owns the main proof successors and final closure. Existing functor owners are preserved in `593ef603-6672-4424-976c-14e11e920d9c`. |

The actual standard families, evaluation topology and representative-sensitive
root action are implemented. The named all-test structural assertions,
topology instances and subgroup comparisons, root/Coxeter realization,
compact-limit inputs and modulus comparisons remain distinct obligations
where their proofs have not been supplied. The public constructions do not
settle these consumer requirements. Only the parent's itemized external
structural list may remain conditional at final parent completion.

## Classification and import audit

No target above has a classification premise. This does not establish
classification independence. A refreshed static scan of the implemented
modules in exact published Library
`6820dc99b5972ed5761be21b4ac8afeba7584644` finds the following project
import closures. There is no private-draft or frozen-candidate overlay. The scan follows
`Langlands.*` imports recursively, counts the entry module and each
reachable project module once, and reports no missing project imports.
It excludes Mathlib imports and measures module reachability, not
proof-term dependencies.

| Entry | Reachable project modules | Modules with `.Classification.` in their names |
| --- | ---: | ---: |
| `Complex` | 115 | 5 |
| `StandardExactness` | 120 | 5 |
| `CorrectedTheorem36` | 337 | 9 |
| `LeviComplex` | 331 | 9 |
| `TerminalJacquet` | 340 | 9 |
| `RationalStandardComplex` | 419 | 9 |
| `RationalCorrectedTheorem36` | 429 | 9 |
| `RationalTerminalJacquet` | 432 | 9 |
| `RationalSupportCategoryTargets` | 428 | 9 |
| `RationalCorrectedFiltrationTargets` | 437 | 9 |
| `RationalSharpConsequenceTargets` | 428 | 9 |

All six rational-point entries reach exactly the same nine
classification-named modules. The three newly published target pairs were
also checked against their frozen bundle hashes before this scan.

For example, `Complex` imports `General.Parabolic`, which reaches
`CompactCoefficient.GroupTransport`, `CuspidalSupport.CuspidalTensorAssociationProof`,
`CuspidalSupport.CuspidalTensorStatement` and
`Classification.SupercuspidalSupport`.
The support-category targets also reach that module through
`Category.ConstituentDichotomy`. Other reachable modules include
`Classification.SupercuspidalContragredientAux`,
`SupercuspidalContragredientStatement`, `SupercuspidalTwist`, `Supercuspidal`,
`Segments`, `ConstituentRelations`, `FiniteLengthStatement` and
`FiniteLengthProof`. Reachability neither proves use of a classification
theorem nor licenses an independence claim. These counts are reproducible
by following the imports of the named modules in that public tree; they do not
inspect declaration bodies or the dependency closure of any later proof.

For the mathematical proof route, Ban–Jantzen Proposition 4.1(3), p.158,
explicitly invokes character independence, Langlands classification and
the geometric lemma for Weyl invariance of induced classes. Theorem 4.2
uses those identities. Any later proof or helper that uses this route
must record that transitive classification dependency. This program
permits it; omission from a target's parameters does not remove it.

The nine classification-named modules in each rational-point entry are
exactly those in the generic target audit. In the construction entry,
`RationalAlternatingOperator → AlternatingOperator` reaches
`Smooth.FiniteLengthGrothendieckTransport → Classification.FiniteLengthProof`
and
`Category.Contragredient → Classification.SupercuspidalContragredientAux`.
The corrected theorem and terminal targets also reach
`SupportCategory → Category.ConstituentDichotomy →
Classification.SupercuspidalSupport`.

These are module-reachability observations, not a declaration-body dependency
audit or a certificate of classification independence. The intrinsic adapters
prove their stated evaluation and quotient laws; there is no main exactness,
Jacquet-comparison or irreducibility proof here whose transitive proof
dependencies could already be certified. Any future use of the
Ban–Jantzen Proposition 4.1(3) route must still record its Langlands
classification, character-independence and geometric-lemma dependencies.

## Registered sources and direct reading

The registered files are those linked in the
[general source map](general-program-source-map.md). All three hashes were
recomputed and matched on restoration on 2 November 2026. The direct reading below is
Worker 194's restoration check; it does not expand another author's
reading record.

| Registered source | SHA-256 | Directly read original passages |
| --- | --- | --- |
| `aubert-1995-duality` | `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693` | Printed pp.2186–2189 / PDF pp.8–11, text: terms, quotient maps, orientations, failed proof step, original use of Proposition 3.2 and Corollary 3.9. The final page explicitly states the class formula, irreducibility and representation biduality; these require the separate proof obligations above. |
| `aubert-1996-duality-erratum` | `d76b3ef9ea2310d1a3129da990c1abd6c304027e3e939a5a1f06c666978c145f` | Printed pp.4687 and 4690 / PDF pp.1 and 4, text: full-smooth support definition, truncated theorem, cokernel and both Levi comparisons. |
| `ban-jantzen-2016-duality` | `7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4` | Printed pp.158 and 160–162 / PDF pp.6 and 8–10, text: classification dependency, truncation issue, two-sided supports and actual graded-transition integrals. |

The complete registered secondary
`aubert-duality-audit-2026-08-13` was also read, with hash and broader
reading extents retained in the general source map. Its correction
guidance is not a proof receipt. The natural-isomorphism formulation and
the complement/universe implementation are internal choices explained
above, rather than claims that these exact Lean interfaces appear in
the literature.
