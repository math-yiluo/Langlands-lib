# General Aubert duality: five-family coverage and remaining proofs

Historical snapshot: the declaration and pending-target inventory below is
pinned to 2 November 2026 and commit `0ebc0efd383ff160084af3b33ab2b7806f7a1dde`.
Use the [3 November declaration and dependency matrix](general-program-dependency-matrix.md)
for the later rational targets, verified proof evidence and retained premises.
The body below preserves the earlier state.

This is an intermediate coverage snapshot for the standalone general Aubert
program, task `46df6a68-5db4-4428-8044-05151d6ce1f6`, revision 1. The public
declarations below refer to Library commit
`0ebc0efd383ff160084af3b33ab2b7806f7a1dde`, checked on 2 November 2026.
Worker 76 assembled the snapshot using Worker 164's structural reconciliation,
Worker 23's shared draft and Workers 585/34's staged GL target inventory.

The [corrected source map](general-program-source-map.md) supplies the original
reading record, exact source locators and conventions. The
[Chapter V ledger](../renard/chapter-v-structural-inputs.md) supplies the finite
S01–S23 external structural boundary and retained D01–D08 obligations. This
note reuses those reviewed source accounts; it makes no new original-literature
audit claim. It supplies no new Lean theorem and does not complete any of the
five families.

“No final target recorded” below means that no public final declaration at the
required general scope has been supplied to this assembly. It does not deny
the existence of generic helpers or GL-specific results. A proposition
definition is a target, and a conditional constructor does not prove its input
predicates. Pending candidates and unreviewed drafts are listed separately.

## Scope and hypothesis boundary

The general results concern actual rational points of a connected reductive
group over an arbitrary nonarchimedean local field, including the permitted
positive-characteristic, nonsplit, nonquasisplit and empty-relative-root cases,
with complex coefficients. The same actual standard family must be used
throughout, with

`W = N_G(T0)/Z_G(T0)`, `W_I = N_(L_I)(T0)/Z_G(T0)`,
and `L_empty = Z_G(T0)`.

Only the external S rows actually consumed by a final theorem may remain
visible structural hypotheses. The D rows and all representation theory remain
proof obligations. In particular exactness, admissibility, finite-length
preservation, adjunctions, the geometric lemma, cuspidal support, induced-class
Weyl invariance and classification are not additional external structural
fields. Prospective S/D needs below are source-level routing information;
they are not a list of hypotheses of final Lean theorems that do not yet exist.

Two required D04 comparisons for the shared actual family are
`|J| = dim(A0) - dim(A_LJ)` and
`|S| - |J| = dim(A_LJ) - dim(A_G)`.
The full character lattice retains central directions. D07 includes the
quotient-modulus orientation
`delta_(P\G) = delta_G/delta_P = delta_P^-1`
and the possibly nonreduced exponent `m_alpha + 2*m_(2alpha)`.
Actual positive induction and inverse Jacquet half-twists must be compared
with this character.

## Public declarations by result family

### 1. Actual exact group and unadjusted operator

Source: Aubert pp.2180–2181, identities (1.1)–(1.4), Definition 1.5.
All names in the first three rows have prefix
`Langlands.SmoothRep.FiniteLengthGrothendieckGroup`.

| Available declaration | Exact scope and remaining general obligation |
| --- | --- |
| [`FiniteLengthGrothendieck`](../../Langlands/Representation/Smooth/FiniteLengthGrothendieck.md): the actual group, `ofRepresentation`, `ofRepresentation_shortExact` | Quotient of actual smooth finite-length representations by all actual short-exact relations, including nonsplit ones; independent coefficient, group and carrier universes. Apply it to the shared actual group. |
| [`FiniteLengthGrothendieckFunctor`](../../Langlands/Representation/Smooth/FiniteLengthGrothendieckFunctor.md): `map`, `map_id`, `map_comp`, `map_eq_of_iso` | Descent requires `PreservesFiniteLength` and `PreservesFiniteLengthShortExact`. The last comparison requires an actual natural isomorphism. Prove those conditions for the general normalized functors. |
| [`FiniteLengthGrothendieckTransport`](../../Langlands/Representation/Smooth/FiniteLengthGrothendieckTransport.md): `pullbackEquiv` | Proved generic K0 transport along an actual continuous group equivalence. Construct the actual conjugations and compare their normalized functors, including distinct normalizer lifts. |
| [`RootSubsetExpansion`](../../Langlands/Representation/Aubert/RootSubsetExpansion.md): `Langlands.Aubert.alternatingOperator_eq_rootSubset_sum` | Reindexes the existing GL operator. It does not define the general reductive operator or identify it with GL. |

No public final general induction/Jacquet/operator or smooth-contragredient
adapter target is recorded here. The full general preservation, exactness and
duality comparisons remain open. Actual group, character and topology work
uses the relevant S01–S16 and S19–S23 inputs; D01/D04/D06/D07 and the
representation-theoretic deductions remain proofs.

### 2. Formal identities and Corollary 1.10

Source: Theorem 1.7, pp.2181–2183; Corollary 1.10, p.2183.
Names in this table have prefix `Langlands.Group.RelativeWeylIndexing` and
are in [`RelativeWeylIndexingTargets`](../../Langlands/Group/RelativeWeylIndexingTargets.md),
with constructions in
[`RelativeWeylIndexing`](../../Langlands/Group/RelativeWeylIndexing.md).

| Public intermediate target or construction | Remaining obligation |
| --- | --- |
| `minimalityLengthCriterion`, `minimalRepresentativeUnique`, `standardIntersection` | Intrinsic Coxeter propositions, with arbitrary Coxeter-system parameters and finite subsets. Their existence as targets proves none of these assertions. |
| `intersectionMultiplicity`, `solomonCancellation`, `jacquetCancellation` | The first constructs a finite count. The latter two are signed-cancellation targets. Actual Levi equality and actual induced classes still require separate comparisons. |
| `longestRep`, `longestRepresentativeUnique`, `longestSurvivor`, `associatedSubsetLaws` | The construction gives membership and maximality in `D(J,empty)`; the named targets retain uniqueness, survivor and associated-subset proof work. Positivity must recover `J' = w_J^-1(J)`, not just reflection images. |
| `ActualCoxeterSystem`, `actualLeviWeylIdentification`, `actualLeviIntersection`, `actualAssociatedLeviConjugation` | The last three are realization targets with an explicit arbitrary subgroup family `L`. They do not prove the required identifications for every `L`. Instantiate the one actual standard family and prove its laws. |

No final general induction identity, associated-Levi Jacquet identity,
smooth-dual commutation, involutivity, cuspidal sign, Corollary 1.10 eigenvalue
or rank-one constituent-exchange target is recorded here. The rank-one branch
needs its actual length-two and constituent-Jacquet assertions.

S08–S18 locate the structural Weyl/root/Bruhat inputs. D06 retains actual
Levi-quotient images, faithful subset indexing, scheme-normalizer versus
point-group-normalizer comparisons, every-lift conjugation, positive-root
recovery and pointwise intersection comparisons. Solomon cancellation is
separate proof work: Aubert's Carter 2.7.7 citation is not S18's Carter 2.7.3.
The geometric lemma and induced-class Weyl-conjugacy theorem remain
representation proofs. The Ban–Jantzen route's use of Langlands classification
is permitted, but its actual general inputs must be proved.

### 3. Corrected actual complex and terminal module

Source: Aubert pp.2186–2187; erratum pp.4687–4690; Ban–Jantzen §4,
pp.160–162, with the corrections in the source map.

| Public construction or theorem | Exact scope and remaining obligation |
| --- | --- |
| [`LocalizationTransition`](../../Langlands/Representation/Jacquet/LocalizationTransition.md) and [`SubgroupTransition`](../../Langlands/Representation/Aubert/SubgroupTransition.md): `Langlands.Aubert.SubgroupTransition.term`, `map`, `map_eval`, `map_refl`, `map_comp`, `augmentation` | Actual subgroup quotients and canonical maps, without finite length. The subgroup terms use trivial-character unnormalized coefficients. Identify them naturally with the shared normalized `i_J r_J`, including cancellation of half-moduli and compatibility of actual transition maps. |
| [`SubgroupComplex`](../../Langlands/Representation/Aubert/SubgroupComplex.md): `Langlands.Aubert.SubgroupComplex.diagram`, `differential`, `differential_square`, `degreeObject` | Signed smooth complex for a finite linearly ordered root index and an actual subgroup family with `P` antitone, `U` monotone and normalization. Instantiate these hypotheses for the shared actual family. |
| Same module: `Terminal`, `terminalRepresentation`, `terminalProjection`, `terminalProjection_surjective`, `terminalProjection_ker`, `terminalObject` | Actual canonical terminal cokernel in an explicit degree; the degree-zero boundary is zero. Choose degree `|S|-|I|` and prove the actual `E#` comparison. These construction laws do not assert exactness or vanishing of this quotient. |
| [`BooleanIntervalComplex`](../../Langlands/Representation/Aubert/BooleanIntervalComplex.md): `Langlands.Aubert.CutComplex.BooleanInterval.exact_of_free_coordinate`, `singletonDegreeEquiv`, `exact_below_allowed` | Generic complex over any complex coefficient module, with no representation-length premise. Identify the actual graded maps and signs before applying contraction, retain the singleton coefficient, and lift through the finite filtration. |

No public final general corrected-exactness or erratum p.4690
associated-Levi Jacquet target is recorded here. Required scope is every smooth
`E` in `Alg({I})`, defined through all irreducible subquotients and their
cuspidal supports. Finite length is not an extra premise.

The actual removed-root family is `P s = P_(S\s)`, `U s = U_(S\s)`,
with `P_S=G` and `U_S=1`. The terminal degree is `|S|-|I|`; when `I=S`
the surviving module must be `E`. No terminal zero may annihilate it.

The repair requires both-sided support
`theta^(J,I) = {x in theta | W_J x W_I ⊆ theta}`,
comparison of consecutive modified supports, and the remaining-length
inequality `length(other) ≥ length(w)` to prove minimality before the
geometric lemma. The actual surviving transition maps must become coefficient
identities up to exterior signs. Isomorphic graded objects alone do not give
this. S16's finite orbit bijection also does not supply an order compatible
with orbit closure. These comparisons, support vanishing and filtration
lifting remain proof obligations; Proposition 3.2 and the original Theorem
3.6 proof cannot discharge them.

### 4. Finite-length and irreducible consequences

Source: corrected complex, erratum p.4690, Corollary 3.9 p.2189.

| Public reuse lead | Remaining general obligation |
| --- | --- |
| [`IrreducibleGrothendieckProof`](../../Langlands/Representation/Smooth/IrreducibleGrothendieckProof.md): `Langlands.SmoothRep.irreducibleGrothendieckStatement` | Generic actual irreducible-realization comparison. It can recover an isomorphism from equal irreducible classes only after both actual modules are proved irreducible. |
| [`JordanHolderGrothendieck`](../../Langlands/Representation/Smooth/JordanHolderGrothendieck.md): `Langlands.SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_haveSameJordanHolderFactors` | Equality in actual exact K0 from matching actual factors. It does not identify arbitrary modules with equal K0 classes. |
| [`IrreducibleImageProof`](../../Langlands/Representation/Aubert/IrreducibleImageProof.md): `Langlands.Aubert.irreducibleImage` | Existing GL exact-class theorem, over `PadicField`. It does not construct general reductive terminal modules or establish their properties. |

No final general target is recorded for termwise finite length, extension
across support types, `D_G[E] = (-1)^|I| [E#]`, nonzero irreducibility of
`E#`, support retention or actual biduality `(E#)# ≃ E`. These require the
general complex, actual length and nonvanishing arguments and involutivity.
They inherit the structural inputs actually used by families 1–3; their
representation assertions are not external S rows.

### 5. GL specialization and whole Zelevinsky comparison

Source: Definition 2.1, Remark 2.2 and Theorem 2.3, pp.2184–2185.
The following Aubert names have prefix `Langlands.Aubert`.

| Public construction or target | Exact scope and remaining obligation |
| --- | --- |
| [`ParabolicQuotient`](../../Langlands/Group/GL/ParabolicQuotient.md): `Langlands.GeneralLinear.BlockShape.parabolicQuotientLevi`; [`RootSubsetExpansion`](../../Langlands/Representation/Aubert/RootSubsetExpansion.md) | Actual GL quotient-Levi and root-subset constructions. The common general datum has not been specialized: algebraic points, topology, actual subgroups/roots, Haar/block half-modulus and functor/operator equalities remain. Existing representation declarations use `PadicField`, so arbitrary-local-field transport is separate. |
| [`GradedGrothendieck`](../../Langlands/Representation/Aubert/GradedGrothendieck.md): `GradedGrothendieckGroup`, `gradedMultiplication`, `gradedUnit`, `BinaryProductExactnessStatement`, `GradedInductionRingLawsStatement`, `gradedInductionRing` | Actual graded exact K0 over all natural ranks. Binary separate exactness is a target; ring laws take arbitrary explicit `hx`. Associativity, commutativity and both unit laws remain targets, not conclusions of the conditional ring constructor. The zero branches use genuine GL0 tensor/unit constructions. |
| [`ProductLeviGrothendieck`](../../Langlands/Representation/Aubert/ProductLeviGrothendieck.md): `binaryProductLeviTensorFunctor`, `ProductLeviTensorPrerequisitesStatement`, `productLeviTensorMap`, `ProductLeviTensorBijectiveStatement`, `productLeviInductionTensorMap_eq` | Positive block ranks, supplied topology and independent field/carrier universes. Prove finite-length preservation, both separate exactness properties and bijectivity for this specific tensor map. Its output is product-Levi K0; induction to GL of rank `a+b` is subsequent. |
| [`SupportSign`](../../Langlands/Representation/Aubert/SupportSign.md): `supportSign`, `supportSign_of_support`, `adjustedOperator`, `adjustedOperator_irreducible`, `adjustedOperator_rankZero` | Actual support adjustment, using existing GL effectivity/support/Jordan–Holder results, including identity on degree zero. Product compatibility is additional proof work. |
| [`SegmentSocleHeadProof`](../../Langlands/Representation/Aubert/SegmentSocleHeadProof.md): `segmentSocleHead`; [`SegmentGrothendieck`](../../Langlands/Representation/Aubert/SegmentGrothendieck.md): `alternatingOperator_segmentSocleClass` | Existing actual segment formula with unadjusted exponent `degree-length`, matching `n-k`. The supplied-constituent theorem and chosen-constituent construction have different input scopes. Neither proves the whole-ring comparison. |

Whole-ring equality needs actual adjusted product/unit/segment identities and
a proved polynomial bijection or spanning by all segment monomials, including
the empty unit. Individual segment variables do not form the additive basis.
Zelevinsky involutivity remains a separate proof obligation. The source's
classification/triangularity and subdivision routes require their exact proved
versions, not merely citation or the existence of polynomial constructors.

## Pending candidates and unreviewed design

This inventory records work outside the public-declaration table. Status is
historical at the inspection described here; identifiers locate candidates or
tasks, not imported Lean dependencies.

| Unit | Evidence and scope boundary |
| --- | --- |
| General A draft, task `593ef603-6672-4424-976c-14e11e920d9c`, Workers 23/1180 | Worker 23's shared draft revision 1, content key `190d77087956b751f8481c1c5e6e7af627dfc00b51e35b8708cb145fc4aff697`, was read in full. `General.Parabolic` and `General.AlternatingOperator` give generic normalized full-smooth functors, an objectwise term comparison and conditional K0/operator constructions. It is unreviewed. Finite-length/exactness predicates, actual reductive realization, naturality and actual-transition comparisons remain obligations. Unimodularity belongs to D07. |
| Actual multiplicity targets, candidate `c1317573-5135-4aae-a15a-48e206331c14` | Machine validation and Reviewer 8665 approval were inspected, with staged/nonpublic status. `actualIntersectionEqualityCriterion`, `actualMultiplicityComparison`, `actualSolomonCancellation` are targets. The helper `actualMultiplicityComparison_of_equalityCriterion` proves only the conditional finite-count implication. |
| Binary exactness proof, candidate `ff617015-48a0-41f6-9fba-9052e7424e06`; minimum proof, candidate `0ba0cde7-c91b-40ec-9212-1de3ce5ef1dc` | Both had machine validation and independent approval but remained unpublished at the assembly's preceding inspection. Their proof sources are not adopted as public dependencies here. |
| Tensor prerequisite proof, candidate `c1a7d667-1848-4cbb-9860-2a2015f7a7a1` | Fresh inspection found machine build/exact-target validation and Reviewer 8817 approval, still staged with accepted=false/public=false. It targets `ProductLeviTensorPrerequisitesStatement`, not tensor bijectivity or induction equivalence. |
| Remaining focused proof assignments | Ring laws: `9c4ccb8b-9e21-4e2a-988b-e7516521079a`; positive tensor bijectivity: `1adb07fa-c4ad-49a0-a523-358b7053a244`. Preserve arbitrary explicit `hx`/`hp`, all-ranks ring scope and independent universes. |
| GL final-target inventory | `ZelevinskyPolynomial`, `GradedOperatorComparison` and `ZelevinskyComparison` have separately staged pairs. Their polynomial, monomial, adjusted multiplicativity, involutivity and final comparison Props are not adopted as public final targets in this snapshot. |

The shared actual-group route still requires standard parabolics and Levis,
characters/split components, actual relative Coxeter realization, rational-point
topology, and one common S19–S23 adapter. The last must retain both opposite
radicals, one simultaneous compact-open basis, uniform containment and
cofinality, continuity transports and a chamber witness including empty roots.
Its localization consumer is
`Langlands.Jacquet.Localization.IsLimitOfCompactSubgroups U`:
every compact subset of the actual subtype `U` is contained in a compact
subgroup of `U`. Exhaustion alone is insufficient. This condition does not
prove induction exactness or first adjunction.

## Dependency accounting still required

For every final theorem in all five families, transitive use of Langlands
classification is **undetermined** until its actual proof root exists and is
audited. The generic K0 results, finite combinatorial targets, actual complex
constructions and existing GL proofs must be distinguished in that audit.
Classification-origin module names or constant counts alone are not a verdict:
such modules also contain elementary definitions and module proofs.

The final matrix must name the exact theorem and proof declarations, list only
the S hypotheses actually consumed, identify all representation and D-row
proofs, record corrected grade-map/filtration inputs and give the precise
classification versions reached through proof types and bodies. The standalone
program permits classification; upstream consumer eligibility is a separate
decision. This intermediate note leaves every final proof and hypothesis
discharge open.
