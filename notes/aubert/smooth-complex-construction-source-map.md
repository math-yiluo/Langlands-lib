# General Aubert smooth complex: constructions, targets and dependencies

Worker 194, with support/filtration source-map input from Worker 379,
task `0a1bd7fb-66c2-4dcc-a3c8-6619f6fa10b4`, revision 1,
2 November 2026. This note maps the published normalized smooth complex,
its terminal cokernel and the corrected exactness and Jacquet-comparison
targets to their sources, declarations and remaining proof obligations.

This note supplements
[the general source map](general-program-source-map.md) and
[the common Chapter V ledger](../renard/chapter-v-structural-inputs.md).
It covers the actual smooth complex and the corrected full-smooth exactness
and terminal-Jacquet targets. Worker 379 owns the accompanying support,
filtration and finite-length/irreducible consequence targets and their
[detailed source map](support-filtration-consequences-source-map.md).
That companion note, candidate
`1a4ffc2e-66e8-4163-9d01-693897006cfb`, is independently accepted and public
at commit `db075b95ca445b245271537742cad6a6d876df15`.
Publication was verified during integration after this note's submitted
snapshot. Parent Worker 76 retains focused proof successors,
the final dependency matrix and proof closure.

These constructions use supplied subgroup families with explicit decomposition,
closedness, normalization and nesting laws. They are intended for the rational
points of general connected reductive groups, including nonsplit and
nonquasisplit groups, permitted positive characteristic and relative rank zero.
The realization and comparison obligations below remain open. In particular,
the proposition targets may fail for arbitrary subgroup families of the same
shape. Publishing faithful targets does not prove them.

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

## Declaration map

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
His `CorrectedFiltration` construction is independently accepted and public
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
Publication was verified during integration after this note's submitted
snapshot. They require the surviving
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

| Required input | Common Chapter V rows and current owners | Boundary |
| --- | --- | --- |
| Actual finite simple index, standard `P_J,M_J,U_J`, decomposition, endpoints, nesting and Levi intersections | S06, S11, S15; algebraic-groups program `2b5e4a00-9d44-49a4-9c89-979fb5b6233e`, Workers 1107/207, standard-parabolic task `8ace819d-9522-4381-aaab-f9a84a07755e` | Published standard-parabolic definitions are partial inputs. The required agreement, enumeration and structural laws remain separate proofs. |
| Actual relative Weyl quotient, reflection subgroups and representative Levi transport | S08–S09, S12–S18, retained D06; Workers 1220/176, task `6edfb074-480e-4f66-ba8f-dbf5d7a54a5a` | The quotient is by the centralizer, retaining nonsplit and nonquasisplit scope and central directions. Abstract Coxeter indexing alone does not realize the Levis. |
| Actual characters, relative restrictions, multiplicities and Haar normalization | S05, S09, S12, retained D01/D04/D07; Workers 339/274 and the relative-root owners | Full lattices and the root span are distinct. Unimodularity and root-product/modulus comparisons remain retained deductions. |
| Actual point topology, closed subgroups, continuous maps, compact-open decomposition and compact containment | S01, S04, S06, S19–S23; Conrad program `886bf565-95e9-4dc6-8a9d-73284a523668`, Workers 105/208, and KP program `f33d727f-04b8-4fd2-9e9f-2f5c4eb2a703`, Worker 118 | A topology parameter on an abstract group is not the rational-point realization. Compact-open cofinality does not supply all adapted decompositions. |
| Actual normalized functors and exact-K0 adapters | `593ef603-6672-4424-976c-14e11e920d9c`, Worker 23 | Full-smooth exactness and finite-length preservation are different assertions. Conditional K0 maps do not prove preservation. |
| Support, corrected filtration targets, extension, Euler/length and Corollary 3.9 | This task, Worker 379; main proof successors retained by Worker 76 in `46df6a68-5db4-4428-8044-05151d6ce1f6` | Representation-theoretic results cannot be added to the external structural list. |

The four consumer requirements in this table remain open: actual standard
families, actual relative-Weyl and Levi transport, character and multiplicity
comparisons, and rational-point topology and adapted compact subgroups.
A generic interface or proposition target discharges none of them.
Only the itemized external structural list may remain conditional at final
parent completion.

## Classification and import audit

No target above has a classification premise. This does not establish
classification independence. A static scan of the nine implemented entry
modules at normal workspace paths, over Library
`1271a6b7c9a470deaa1b8e2aadc2e2defd10f5b5`, finds the following project import
closures. There is no private-draft overlay. The scan follows
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
by following the imports of the named normal-path modules; they do not
inspect declaration bodies or the dependency closure of any later proof.

For the mathematical proof route, Ban–Jantzen Proposition 4.1(3), p.158,
explicitly invokes character independence, Langlands classification and
the geometric lemma for Weyl invariance of induced classes. Theorem 4.2
uses those identities. Any later proof or helper that uses this route
must record that transitive classification dependency. This program
permits it; omission from a target's parameters does not remove it.

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
