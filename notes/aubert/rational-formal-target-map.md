# General Aubert identities on actual rational points: source and target map

This addendum records the actual connected-reductive specialization for task
`e3d69272-2599-4a08-a934-cb11f2493e30`, revision 1. It complements the
[finite/subgroup table](relative-weyl-construction-target-map.md) and the
[generic representation table](general-formal-target-map.md), whose evidence
sections describe earlier inspections. It identifies the actual constructions,
complete premise groups of thirteen representation targets, published reuse
and remaining proof owners. It proves no main identity and declares neither
this task nor its parent complete.

Names below have prefix `Langlands.Aubert.General.RationalPointFamily`
unless another namespace is given. Every `Rational…Statement` listed here
is a Prop-valued declaration, not a proved instance.

## Actual scope and complete premise groups

The actual group is `RationalPoint k G.X` with the explicitly installed
canonical evaluation topology `pointTopology`. The torus subgroup is the
literal image of the specified torus map on points. The labels are the
membership subtype `SimpleRoot i ν` of actual simple relative characters.
For `I : Finset (SimpleRoot i ν)`, `rootSet i ν I` is their exact character
image; `parabolic`, `levi`, `unipotent` evaluate the existing standard
subgroup functors at this image and the identity test object.
No freely supplied subgroup family replaces them.

The scope includes nonsplit and non-quasisplit connected reductive groups,
positive characteristic and an empty simple-root type. There is no added
characteristic-zero or positive-rank restriction. The quantifiers do not
prove the explicit structural or topological realization premises.

These groups abbreviate the displayed Lean binders; each target row below
gives their full combination and additional representation hypotheses.

| Group | Exact premises and derived constructions |
| --- | --- |
| A | `k : Type u` with `Field`, `ValuativeRel`, `TopologicalSpace`, `IsNonarchimedeanLocalField`; a group scheme G with `hG : IsConnectedReductive G`; a commutative group scheme T, actual `i : T.toGrp ⟶ G` and `hi : IsMaximalSplitTorus i`; a cocharacter ν with `IsGenericCocharacter i ν`; `StandardCocharacterStatement`; closed actual unipotent subgroups `hU`. After installing `pointTopology`, `LocallyCompactSpace`, `NonarchimedeanGroup` and `T2Space` on that exact point group are explicit. Affineness follows from hG, and monomorphy when needed from hi. `isSemidirectDecomposition_of_standardCocharacterStatement` derives the ambient decompositions. |
| R | `hRoots : HasRelativeRootSystem i`. With the torus's splitness it supplies the enumeration `simpleRelativeRootFintype` of the actual simple roots. It supplies no Coxeter or root-sign realization. |
| K | Closed parabolics `hP`, continuity `hproj` of every derived standard projection, compact-subgroup-limit hypotheses `hUc` on the unipotents, and separate finite-length preservation `hiFl`, `hrFl` for actual normalized induction and Jacquet restriction. `standardParabolicFiniteLength` derives short-exact preservation from the published exactness theorems and these topological inputs. No desired identity is among the premises. |
| B | `StandardLeviIntersectionStatement` and closed actual Levis `hM`. The derived `isSemidirectDecomposition_in_levi` supplies the literal restricted families inside each Levi. R is listed separately here. |
| L | B, continuity `hLproj` of the actual restricted projections, compact-limit hypotheses `hLUc` on restricted radicals, and separate restricted normalized induction/Jacquet finite-length preservation `hiLFl`, `hrLFl`. The local compactness of each Levi is obtained from `hM J` with its inherited topology. `standardLeviParabolicFiniteLength` derives restricted exactness for `rationalLeviAlternatingOperator`. |
| W | Finiteness of the actual `Weyl i`; separate exact comparisons `hN : HasPointNormalizerComparison i` and `hZ : HasPointCentralizerComparison i`; a Coxeter matrix on literally `SimpleRoot i ν`; `cs : ActualCoxeterSystem (torusPoints i) CM`; `RootLengthComparison` and `PositiveSimpleReflectionComparison`. The latter compares reflection labels with actual character equality only under positivity. |
| WJ | The distinct intrinsic propositions `minimalityLengthCriterion cs` and `associatedSubsetLaws cs`. With W and finite simple roots, `rootSet_associatedSubset` identifies the associated subset with the actual inverse-longest character image. |
| WG | `actualLeviWeylIdentification (torusPoints i) (levi i ν) cs`: the image of each actual Levi Weyl quotient inclusion equals `standardSubgroup cs I`. Injectivity of the inclusion does not prove this equality. |
| C | `ContragredientPreservesFiniteLength` on the actual point group. Compact-open cofinality for `contragredientK0` is derived from the displayed nonarchimedean locally compact group structure. |
| H | Separate `hGeom : GeometricIntersectionDecompositions` for the literal P/L/U, torus image and cs, and `hTermFl : GeometricTermFiniteLength` for every minimum representative and every lift. The former contains source/target semidirect decompositions only. The latter requires both finite-length and finite-length short-exact preservation for source Jacquet restriction and target induction. Neither contains an expansion equation. |

Representation carriers are `Type (max (u + 1) v)`. The exact K0 is the
published `SmoothRep.FiniteLengthGrothendieckGroup` of actual smooth complex
representations, imposing all actual short exact relations, including
nonsplit ones. Its quotient type universe is not identified with the
representation-carrier universe.

`D_G` is exactly `rationalAlternatingOperator`, the unadjusted sum
`∑_I (-1)^|I| i_I r_I`. The actual normalized maps `inductionK0` and
`jacquetK0` and the operator have published actual-class formulas.
Induction uses the positive half modulus and Jacquet restriction the inverse
half modulus. The compact-limit hypothesis supplies radical unimodularity
needed for the source induction normalization.

For `I : Finset J`, the inside-Levi families are the literal
`subgroupOf (levi i ν J)` restrictions at `leviIndex J I`.
`card_leviIndex` preserves the Levi exponent. Cuspidality means actual
normalized Jacquet zero objects for all proper standard subsets, in the
ambient group or inside the Levi as indicated. Irreducibility is separate;
no admissibility conjunct is added to this predicate.

## The five assertions of Theorem 1.7

The source is Aubert 1995, Definition 1.5 and Theorem 1.7, printed p.2181 /
PDF p.3.

| Actual declaration and pair | Complete premises | Exact target and retained proof work |
| --- | --- | --- |
| [RationalContragredientTarget](../../Langlands/Representation/Aubert/General/RationalContragredientTarget.md): `RationalContragredientCommutationStatement` | A + R + K + C | Part (1): `D_G ∘ c_G = c_G ∘ D_G` as integer-linear maps on whole exact K0. Smooth-contragredient compatibility and realization of finite-length preservation remain. |
| [RationalInductionTarget](../../Langlands/Representation/Aubert/General/RationalInductionTarget.md): `RationalInductionCompatibilityStatement` | A + R + K + L | First equation of (2): for every J, `D_G ∘ i_J = i_J ∘ D_(L_J)`, with no extra rank sign. The Levi operator uses the actual restricted families. Transitivity, geometric expansion, cancellation and induced-class conjugacy belong to the proof route. |
| [RationalJacquetTarget](../../Langlands/Representation/Aubert/General/RationalJacquetTarget.md): `RationalJacquetCompatibilityStatement` | A + R + K + L + W + WJ + `StandardLeviConjugationStatement` | Second equation of (2): `r_J ∘ D_G = Ad(n) ∘ D_(L_Jprime) ∘ r_Jprime`, for every J and every lift n of the specified `longestRep cs J` in `D(J,∅)`. `Jprime = associatedSubset cs J` has character set `w_J⁻¹(J)`. The named structural conjugation statement derives actual transport; no arbitrary associated-Levi witness replaces it. WG is not a premise. |
| [RationalInvolutivityTarget](../../Langlands/Representation/Aubert/General/RationalInvolutivityTarget.md): `RationalInvolutivityStatement` | A + R + K | Part (3): `D_G ∘ D_G = LinearMap.id` on the entire exact K0 group. No involutivity law is supplied as input. |
| [RationalCuspidalEigenvalueTarget](../../Langlands/Representation/Aubert/General/RationalCuspidalEigenvalueTarget.md): `RationalCuspidalEigenvalueStatement` | A + R + K; actual irreducibility and ambient proper-standard Jacquet vanishing | Part (4): `D_G[A] = (-1)^\|S\| [A]` for `S = SimpleRoot i ν`. The published `hasFiniteLength_of_isIrreducible` supplies finite length. The full-subset identity term and eigenvalue proof remain required. |

The associated-Levi adapter derives `n L_Jprime n⁻¹ = L_J` for every
specified lift. Inverse conjugation is the continuous equivalence from
`L_J` to `L_Jprime`, so forward representation transport acts by
`σ(n⁻¹ x n)`. Independently, the character action uses inverse pullback
`σ.inv ≫ χ` for a normalizing torus automorphism σ. The quotient
comparisons preserve actual normalizer representatives throughout.
Lift independence of subgroup images does not equate elementwise
conjugation maps or establish equality of induced classes.

If S is empty, the operator has the single positive term `i_∅ r_∅`.
Identifying it with the identity still requires actual endpoint comparisons.
The full centralizer retains central and anisotropic directions. The sign
exponents are root cardinalities; the rank comparisons remain
`|J| = dim A0 - dim A_(L_J)` and
`|S|-|J| = dim A_(L_J) - dim A_G`, not total split rank.

## Geometric expansion and separate induced-Weyl conjugacy

| Actual declaration and pair | Complete premises | Source, conclusion and proof boundary |
| --- | --- | --- |
| [RationalGeometricK0Target](../../Langlands/Representation/Aubert/General/RationalGeometricK0Target.md): `RationalGeometricK0ExpansionStatement` | A + R + K + closed Levis `hM` + W + WG + H | Aubert (1.3), p.2181: for all I,J and every section of the actual normalizer quotient, `r_I ∘ i_J` is the sum of actual `geometricTermK0` maps over `D(I,J)`. WJ, `StandardLeviIntersectionStatement` and `StandardLeviConjugationStatement` are not premises. No filtration or expansion proof is supplied. |
| [RationalInducedWeylConjugacyTarget](../../Langlands/Representation/Aubert/General/RationalInducedWeylConjugacyTarget.md): `RationalInducedK0WeylConjugacyStatement` | A + K; every actual normalizer n carrying `L_I` onto `L_J` | Aubert (1.2), p.2181; Ban–Jantzen Proposition 4.1(3), p.158: `i_J ∘ Ad(n) = i_I` on exact K0. It directly quantifies actual normalizer elements and needs no R, finite enumeration, Coxeter system, hN or hZ. |
| Same pair: `RationalInducedClassWeylConjugacyStatement` | A + K and the same actual normalizer/Levi transport hypotheses | Equality of actual normalized induced representation classes for all finite-length inputs, not an induced-representation isomorphism. Continuous-equivalence pullback supplies transport finite length. Generator formulas and `hom_ext_object` support comparison with the map-level formulation. |

For a minimum representative with lift n, the geometric terms use exactly:

| Role | Source inside `L_J` | Target inside `L_I` |
| --- | --- | --- |
| Parabolic | `L_J ∩ n⁻¹ P_I n` | `L_I ∩ n P_J n⁻¹` |
| Levi | `L_J ∩ n⁻¹ L_I n` | `L_I ∩ n L_J n⁻¹` |
| Radical | `L_J ∩ n⁻¹ U_I n` | `L_I ∩ n U_J n⁻¹` |

Each term is actual source Jacquet restriction, forward-n representation
transport by inverse pullback, then actual target induction. The generic
`General.GeometricK0Target` supplies these functors, exact maps and class
formula. The specialization introduces no freely chosen term maps or
expansion witness.

Worker 14 retains the actual geometric filtration and orbit graded pieces.
Its `P_J n⁻¹ P_I` convention on `P_J \ G / P_I` needs the inversion
comparison with `W_I \ W / W_J`. Both Haar corrections, modulus and
half-modulus comparisons, smooth realization, graded-piece identification
and any compact/full-induction comparison remain. After these comparisons,
the published `SmoothRep.filtrationGrothendieckStatement` supplies exact K0
additivity; citing it alone does not specialize the filtration.

Induced-Weyl conjugacy is a separate representation-theoretic obligation.
Aubert cites Bernstein–Deligne–Kazhdan Lemma 5.4(iii) for (1.2).
The permitted Ban–Jantzen route explicitly uses character independence,
Langlands classification and the geometric lemma. A successor following it
must name the actual general proof declarations and hypotheses. These targets
provide no classification theorem or classification-independence result.
None of these inputs belongs in the final external Chapter V boundary.

## Corollary 1.10 and three named prerequisites

All five declarations are in
[RationalCorollaryTargets](../../Langlands/Representation/Aubert/General/RationalCorollaryTargets.md).
The source is Aubert 1995, Corollary 1.10 and proof, printed p.2183 /
PDF p.5; cuspidality is defined on p.2181.

| Actual declaration | Complete premises | Exact conclusion and remaining route |
| --- | --- | --- |
| `RationalCorollary110aStatement` | A + R + B + K; irreducible inside-Levi cuspidal σ and irreducible actual normalized induction | For every J, `D_G[i_J σ] = (-1)^\|J\| [i_J σ]`. The intended proof uses induction compatibility and the Levi cuspidal eigenvalue. The source induction-irreducibility premise is retained. |
| `RationalCorollary110bStatement` | A + R + B + K; `J = univ.erase α`; irreducible inside-Levi cuspidal σ with reducible actual normalized induction | An actual length-two series with irreducible factors and both equations `(-1)^\|J\| D_G[ρplus] = [ρminus]` and `(-1)^\|J\| D_G[ρminus] = [ρplus]`. The three prerequisites below, exact additivity, actual top term and induced-K0 Weyl conjugacy belong to the proof route. |
| `RationalRankOneLengthTwoStatement` | A + R + B, without K; the same maximal-Levi, cuspidality, irreducibility and induction-reducibility hypotheses | An actual length-two series. `HasTwoConstituents` uses an actual short exact sequence in either factor order; no splitting is assumed. |
| `RationalRankOneSelfAssociationStatement` | A + R + B + W + WG + WJ, without K; the same representation hypotheses | `associatedSubset cs J = J`, and every specified longest lift normalizes the literal actual Levi. Reducibility forcing self-association remains representation theory. |
| `RationalRankOneJacquetModulesStatement` | A + R + B + W + WG + WJ, without K; the same representation hypotheses | For every specified longest lift and its self-normalization witness, two irreducible factors can be labeled so `r_J ρplus ≅ σ`, `r_J ρminus ≅ Ad(n⁻¹) σ`, and both Jacquet objects vanish for every other proper standard subset. The second action is `σ(n x n⁻¹)`. |

The three prerequisite targets concern actual objects and do not quantify K.
This proves no finite-length, admissibility or exactness theorem needed by
their future proofs. The length-two series is part of the conclusion of (b);
the sign is `(-1)^|J|`, while maximality gives `|S| = |J| + 1` for its
separate top-term calculation. Part (a) includes J empty. Part (b) and the
three rank-one targets have no maximal label when S is empty, so their
implications are vacuous.

Casselman §7.1, pp.67–68, Corollary 7.1.2 and Theorem 7.1.4 are the
proposed length and self-association route. His admissible and
absolutely-cuspidal setting requires general admissibility and a cuspidality
comparison before application to these predicates. Nonzero induction,
finite length and actual factor realization must also be supplied. A citation
does not discharge applicability or the Jacquet-pattern proofs. GL-specific
tempered-induction irreducibility does not replace these general hypotheses.

## Construction and published reuse map

These pairs provide actual objects and conditional helper proofs. Realization
propositions remain targets wherever indicated.

| Pair | Reused construction or conditional consequence | Retained premises and limitations |
| --- | --- | --- |
| [RationalPointFamily](../../Langlands/Representation/Aubert/General/RationalPointFamily.md) | Exact simple-root subtype, injective `rootSet`, literal P/L/U, torus image, canonical topology, `Weyl` and `LeviWeyl`. | Reuses the shared standard-family and point-topology definitions. No fabricated finite instance, endpoint equality or reversed centralizer inclusion. |
| [RationalWeylComparisonTarget](../../Langlands/Representation/Aubert/General/RationalWeylComparisonTarget.md) | `normalizerEquiv`, full denominator transport, `weylEquiv`, representative formulas and conditional finiteness transfer. | The universal `RationalWeylComparisonStatement` is unproved. The equivalence needs hN and hZ; finiteness transfer also needs scheme-Weyl finiteness. |
| [RationalLeviWeylComparison](../../Langlands/Representation/Aubert/General/RationalLeviWeylComparison.md) | `pointStandardWeyl`, conditional centralizer containment, scheme/point standard-image equality and `leviWeylEquiv`, commuting with ambient inclusions. | Both comparisons remain inputs. It proves neither WG nor `L_∅ = Z_G(T0)`. |
| [RationalWeylRootAction](../../Langlands/Representation/Aubert/General/RationalWeylRootAction.md) | Full-centralizer descent of the character action, representative-preserving transport and exact relative-root-set preservation. | hN and hZ remain. No Coxeter or positivity theorem is proved. |
| [RationalRootSignTarget](../../Langlands/Representation/Aubert/General/RationalRootSignTarget.md) | Actual root-image finite sets, conditional positive-image comparisons and `rootSet_associatedSubset` under W + WJ and finite enumerations. | `RationalRootSignCoxeterStatement` remains unproved. Reflection conjugacy alone loses sign; positivity is necessary. |
| [RationalParabolicDecomposition](../../Langlands/Representation/Aubert/General/RationalParabolicDecomposition.md) | Derived ambient decomposition, `standardProjection` and its equality with the actual dynamic limit. | Uses the shared standard-cocharacter proposition and dynamic decomposition; proves no instance of that proposition, topology property or endpoint equality. |
| [RationalAlternatingOperator](../../Langlands/Representation/Aubert/General/RationalAlternatingOperator.md) | Derived exactness, radical unimodularity, actual unadjusted operator and class/empty-root formulas. | Structural, topology, root-finiteness and both finite-length premises remain. The positive single empty term is not identified with the identity. |
| [RationalLeviDecomposition](../../Langlands/Representation/Aubert/General/RationalLeviDecomposition.md) | Elementary `IsSemidirectDecomposition.subgroupOf`, `isSemidirectDecomposition_in_levi` and `standardLeviProjection`. | Evaluates the first clause of `StandardLeviIntersectionStatement`; proves no instance of that all-test proposition. |
| [RationalLeviFiniteLength](../../Langlands/Representation/Aubert/General/RationalLeviFiniteLength.md) | Derived restricted exactness and `rationalLeviAlternatingOperator`. | Restricted continuity, compact-limit and both finite-length premises remain; closedness supplies local compactness explicitly. |
| [RationalAssociatedLeviConjugation](../../Langlands/Representation/Aubert/General/RationalAssociatedLeviConjugation.md) | Exact relative-root-subset encoding, `associatedLeviConjugation_of_standard` and actual inverse-conjugation continuous equivalence. | Evaluates the named all-test `StandardLeviConjugationStatement` at the identity object, using W + WJ for actual inverse-longest images. It establishes no elementwise lift independence or induced-class invariance. |

The quotients use `W = N_G(T0)/Z_G(T0)` and the full centralizer inside
each actual Levi, following Renard V.4.1–V.4.3 and the registered Aubert
audit's correction to the printed torus denominator. Conditional centralizer
containment gives the full denominator inside the Levi. Equality
`L_∅ = Z_G(T0)`, `L_S = G`, faithful subset indexing, WG and the rank
comparisons remain separate structural or derived obligations.

The finite/subgroup companion already lists `solomonCancellation`,
`jacquetCancellation`, `longestSurvivor`, `associatedSubsetLaws`,
`actualIntersectionEqualityCriterion`, `actualMultiplicityComparison` and
`actualSolomonCancellation` separately.
`actualMultiplicityComparison_of_equalityCriterion` proves only the
conditional count equality. Actual/intrinsic intersections and both
subset-faithfulness results remain the route to its premise. Existing
finite-combinatorics proof work, including Worker 835's and parent routing,
is preserved; specialization requires the current published proof's full type.
This table does not replace it with an assumed coefficient identity.

## Inspection evidence and ownership

These actual pairs have independently accepted and published records.
Identifiers locate evidence, not mathematical imports.

| Pair or group | Accepted publication evidence |
| --- | --- |
| Actual family; ambient quotient comparison | `c9404b78-818d-4eec-9bdf-e15abaff5f59` (Reviewer 9091); `fcc267a1-08e1-4ba3-bf4b-5bebc105241e` (Reviewer 9125). Commit `5730d31ad8127eb9e13a5c1e47edacef54dfa8e3`. |
| Levi quotient comparison; root action | `1ea61b09-93fa-4e4e-b820-8ffdb69be65e` (Reviewer 9149); `40d6d364-677f-4cd1-80a5-8ed2dff380aa` (Reviewer 9190). Commit `7a2e42fd31831029d34cafb155ffad911920df25`. Independently owned functor/operator adapter `434a4095-6e40-4821-becc-73e6edef6124` (Reviewer 9160) published separately in that commit. |
| Root-sign target | `b735ebdc-52d0-4175-a05d-6f149dd43574` (Reviewer 9206). Commit `7543113c99690e18b45f3b22d252e8cf77c3964e`. Acceptance of the proposition pair proves no realization instance. |
| Ambient decomposition; actual operator | `9e78159a-76b7-4e2b-8ac8-53a651cc405e` (Reviewer 9273); `f0941184-2804-4e7d-95b7-cb5d590f1f6d` (Reviewer 9299). Commit `286dd3b743f0437d22db0e793222073b9424e3eb`. |
| Involutivity; contragredient; cuspidal targets | `1f7b9c33-1513-4226-b4cb-e69dc8b640a7` (Reviewer 9323); `299d0242-7d02-4f3c-8293-a021f7d2755d` (Reviewer 9345); `ec3a6fda-15b6-4c67-947a-003f6022c94a` (Reviewer 9359). Same commit `286dd3b743f0437d22db0e793222073b9424e3eb`. |
| Restricted decomposition | `d40473ee-7a9a-4603-baa7-e326ccee39b3` (Reviewer 9403). Commit `d3ab507f01d1e2e025d7fd38df0d2b7f78a9e301`. |
| Induced-Weyl targets | `394a769a-fc11-4e0e-b22f-22f0eaae081b` (Reviewer 9478). Commit `1271a6b7c9a470deaa1b8e2aadc2e2defd10f5b5`. |
| Corollary/rank-one targets; corrected Levi operator | `604c6eb5-9bbe-42fb-8ecb-7001365126a9` (Reviewer 9496); `c84aa89b-c8eb-47c1-a574-68b14a359cb2` (Reviewer 9568). Commit `5d3754ec863f6d5013aca65cbcec0801e6972d1f`. Withdrawn predecessor `95ed0330-8e55-49b4-9e2e-68e7607cbdaf` is not evidence. |
| Actual induction target | `b8c6fc5b-effc-4a2e-b0d0-b6c14039779f` (Reviewer 9607). Commit `9d1720cbedcfd184cf48bf36249fc3029583cafa`. |
| Associated-Levi adapter | `f79b3eb0-1a68-4d68-b742-2b55fa657017` (Reviewer 9686). Commit `fe38b3e353a7b1fb30017218b2ee1f7f87f979fd`. |

At this inspection, Jacquet target `915c8161-9ebb-4240-a111-9d6dffa13e97`
had terminal machine acceptance `3b92eff4-50f4-4b80-8e30-c7b7e5559491`
and independent approval by Reviewer 9698, with publication pending.
Geometric target `f039d723-9c7b-4e51-bda9-704049e577d5` had terminal
machine acceptance `93e2d5d5-e5ae-4ef3-9102-ca8484dd2398`, with
independent review and publication pending. Publish these two linked pairs
separately before this addendum. Development recheck
`de8600d3-3e73-44d1-a464-a4ba679bf79f` compiled their modules and the
associated-Levi adapter with zero errors/warnings, inspecting the geometric
target as Prop-valued with standard axioms. This is not semantic acceptance
or an identity proof.

The generic table is independently published as
`3a125444-5a63-4491-bd17-a0b5befd6d6f` (Reviewer 8981), commit
`546440987a08c6f0a563446add611f8ff5c9a372`. Its earlier staged-status
descriptions remain historical. Import mathematical declarations by their
current Lean names.

Worker 165 supplies actual constructions, main/geometric targets and this
assembly; Worker 1186 supplies the induced-Weyl and Corollary specializations
and source crosswalk. Shared standard-family, relative-root and point-topology
constructions retain their owners. Workers 23/1180 retain normalized functor,
transport and exact-K0 ownership; Worker 14 and Renard owners retain geometric
filtration and graded pieces. Existing GL and finite-combinatorics work is
preserved.

Parent `46df6a68-5db4-4428-8044-05151d6ce1f6`, Worker 76, owns focused
proof successors, general-to-GL comparison and final assembly. Shared
standard-Levi-conjugation proof task `2411603b-373b-4dbe-bcde-69047693b293`
retains its owner. Intermediate structural premises do not enlarge the finite
itemized [external Chapter V boundary](../renard/chapter-v-structural-inputs.md).
Admissibility, finite length, exactness, adjointness, transitivity, geometric
expansion, cuspidal support, induced-class conjugacy, classification and main
identities remain representation-theoretic obligations unless exact published
proofs are supplied. Source citations, task titles and target publication
alone do not discharge them.

## Originals and reading record

The [generic reading record](general-formal-target-map.md#original-source-and-reading-record)
and [general source map](general-program-source-map.md) give source and
correction context. This addendum uses the same registered originals:

| Original and SHA256 | Supporting passages and reading |
| --- | --- |
| `aubert-1995-duality`, `57af9c46769f6edd8e142ddaf465e89acfa2f2147db222d26879a28a06df9693` | Printed pp.2180–2183: quotient/longest/conjugation conventions, (1.2), (1.3), Definition 1.5, Theorem 1.7, cancellation and Corollary 1.10. Worker 165 reread pp.2180–2181 and 2183 for the actual specialization; Worker 1186's original visual sign/conjugation check is retained. |
| `renard-2026-representations-groupes-reductifs-padiques`, `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c` | V.3.6–V.3.13 and V.4.1–V.4.6: central directions, full-centralizer quotients, standard families, root images and length. Direct reading is recorded in the finite/subgroup companion. Scheme-to-point and consumer comparisons are internal derivations. |
| `ban-jantzen-2016-duality`, `7885375b64f6146a16d2b7807447bb913e411bf73735877aca2d62f80dd4dac4` | Proposition 4.1(3) and proof, printed p.158 / PDF p.6. The recorded direct reading identifies character independence, Langlands classification and the geometric lemma; it supplies no missing Lean proof. |
| `casselman-1995-admissible-representations`, `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a` | Admissible setting and §7.1, printed/PDF pp.2 and 67–68; recorded direct reading of Lemma 7.1.1, Corollary 7.1.2 and Theorem 7.1.4. Applicability obligations are retained above. |

The registered Aubert audit and 1996 erratum boundary were checked. Theorem
1.7 and Corollary 1.10 are used with the full-centralizer correction.
Proposition 3.2 remains unresolved and unused; neither its invalid proof nor
the invalid original proof of Theorem 3.6 supplies evidence here. No new
external theorem or classification-independence claim is made.

Authors: Worker 165 and Worker 1186. The cited upstream constructions and
earlier reviewed source analyses retain their original attribution.
