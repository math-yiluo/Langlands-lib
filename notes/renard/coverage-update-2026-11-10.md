# Renard 2026: coverage update, 10 November 2026

Worker 1222, executor of the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, revision 1. This note continues the
[coverage update of 9 November 2026](coverage-update-2026-11-09.md) and the
[whole-book ledger](coverage.md). It records the statement units of this task
published since that update, their proof tasks, related tasks of other
workers, and audit findings. It declares no section, chapter or book complete.
A published statement is not a proof; every row keeps the proof status
explicit.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers equal printed page numbers plus six. Library facts refer to
commit `45606b6bf1145d8d8b4633e8eb97477209c366b7`.

## New statement publications

Each unit below is a `lean.statement@1` publication by Worker 1222. Each was
reviewed independently and integrated. Each has a `lean.proof@1` successor
task, which Worker 1222 published after the statement entered the Library.
The III.1.4 statement is proved, and so is one conjunct of the VI.7.2 Theorem
unit (the blocks are abelian); see below the table. For the other seven
propositions, and for the remaining conjuncts of the VI.7.2 Theorem unit,
Worker 1222 found no theorem or published proof term of their types in the
Library: their names occur only in their own statement files (and, for the
abelian conjunct, in its proof).

| Source assertion | Library module and entry declaration | Candidate | Proof task |
| --- | --- | --- | --- |
| I.3.2, remark after (I.3.2.1), printed p.20 / PDF p.26: the complex structures on `A ⊗_{eAe} Z` from `A` and from `Z` coincide | `Langlands.Algebra.NonUnitalModuleCornerInductionComplexScalarsStatement`, `Langlands.Algebra.NonUnitalModuleCornerInduction.ComplexScalarsStatement` | `7c9b1249-ee12-48e8-b928-2539175e44f4` | Task 5342, `115b38ac-7e1e-4790-b21b-ce3c753617f9` |
| III.1.4, Theorem, printed p.60 / PDF p.66: smooth representations are equivalent to nondegenerate `H(G)`-modules | `Langlands.Representation.Hecke.NondegenerateModuleEquivalenceStatement` | `633217b0-5c58-45c4-af2b-096cb96fcf02` | Task 5301, `3b60b71d-9e2e-4dd9-90a7-2c6f770a2d68` |
| III.1.14–III.1.15, printed pp.66–69 / PDF pp.72–75: smoothness of tensor products, the right `H(G)`-action by `π(Ť)`, `(V₁ ⊗ V₂)_G ≅ V₁ ⊗_{H(G)} V₂`, (III.1.15.1), and Remark 3 (twists) | `Langlands.Representation.Smooth.RenardCoinvariantTensorStatements`, `Langlands.Renard.Smooth.RenardCoinvariantTensorStatements` | `ec28f633-5803-4f33-acaf-a624c90b8ec6` | Task 5341, `ea108cfc-df4f-4644-8d5d-f2ea5ca322a3` |
| IV.1.1, multiplicity formula, printed p.89 / PDF p.95; IV.3.3, Corollary, last sentence, printed p.102 / PDF p.108 | `Langlands.Representation.Compact.CompactMultiplicityIndependenceStatements`, `Langlands.Renard.CompactRepresentation.CompactMultiplicityIndependenceStatements` | `b1810817-49da-4c57-85b8-0b2c2dafe398` | Task 5345, `a983ac31-babd-4207-b947-3b9ace4bc1b7` |
| IV.1.6–IV.1.7, printed pp.94–95 / PDF pp.100–101: compact irreducibles are projective and injective, `M(G)_c` is semisimple, and the three block decompositions | `Langlands.Representation.Compact.CompactBlockDecompositionStatements`, `Langlands.Renard.CompactRepresentation.CompactBlockDecompositionStatements` | `ae0cd71a-a099-466d-93fb-f85252e66d46` | Task 5343, `6792dfb2-2c25-4a59-afd8-17c485d7c088` |
| VI.1.1, printed pp.134–135 / PDF pp.140–141: Frobenius reciprocity, exactness and limits for the unnormalized functors `Ind_P^G` and `j_N` | `Langlands.Representation.Exponents.LeviUnnormalizedParabolicStatements`, `Langlands.Aubert.General.RepresentedParabolic.LeviUnnormalizedParabolicStatements` | `5d21135a-155e-4a66-a6d4-e6574c1e8a57` | Task 5344, `7f65d809-e87f-4d4b-984e-e83edae0046c` |
| VI.7.2, Theorem, (VI.7.2.2)–(VI.7.2.3), first Lemma and the remark that blocks are abelian, printed pp.181–184 / PDF pp.187–190 | `Langlands.Representation.CuspidalSupport.BernsteinDecompositionStatements`, `Langlands.CuspidalSupport.BernsteinDecompositionStatements` | `e1048758-8213-4ec4-8fd0-b3753ec1d0b3` | Task 5346, `42ad56a2-0729-42a7-9240-63e953ee2961` |
| VI.7.2, Proposition, printed p.184 / PDF p.190: three characterizations of a Bernstein block (embedding in, or subquotient of, a sum of `i_P^G(τ)` with `τ ∈ M(M)_D`; vanishing of the non-conjugate Jacquet components) | `Langlands.Representation.CuspidalSupport.BernsteinBlockCharacterizationStatement`, `Langlands.CuspidalSupport.BernsteinBlockCharacterizationStatement` | `122d19e0-cf7c-4a1e-9e99-ceb1ff5af879` | Task 5352, `2a804ec7-6b5f-4bbe-93ab-39527f9b50a9` |
| VI.7.4, printed pp.185–186 / PDF pp.191–192: central idempotents `e_𝔰` and the decomposition of `H(G)` into the ideals `S_𝔰` | `Langlands.Representation.CuspidalSupport.BernsteinCentralIdempotentStatements`, `Langlands.CuspidalSupport.BernsteinCentralIdempotentStatements` | `3598eced-40fa-4e45-bb67-2da49475d23b` | Task 5347, `31433303-4514-4dc0-9705-92c0bf9bb8e1` |

The entry declaration of the III.1.4 unit is
`Langlands.Hecke.HeckeNondegenerateModuleEquivalenceStatement`. It is proved:
Worker 155's theorem `Langlands.Hecke.heckeNondegenerateModuleEquivalence`
(module `Langlands.Representation.Hecke.NondegenerateModuleEquivalenceProof`)
has exactly the type `HeckeNondegenerateModuleEquivalenceStatement.{u, v}`.
Its proof artifact `0b481871-b4e8-43f6-bd31-0ca44e10dd1d` was approved by
Reviewer 466 (review `9247c859-04b0-4db0-844d-48e3c43ee8ec`) and published at
commit `e449cde988d4e97ab280b8d4d11262887ccc26e0`. Its proof Task 5301 is
done.

The VI.7.2 Theorem unit `BernsteinDecompositionStatements` is the conjunction
of three statements. Its conjunct `BernsteinBlockAbelianStatement` (every
block is abelian with the inherited preadditive structure) is proved by
Worker 167's theorem `Langlands.CuspidalSupport.bernsteinBlockAbelian` (module
`Langlands.Representation.CuspidalSupport.BernsteinBlockAbelianProof`, Task
5313), proof artifact `457c2586-2eac-464c-ad02-4fdad27331a0`, approved by
Reviewer 526 and in the Library since commit
`e449cde988d4e97ab280b8d4d11262887ccc26e0` at the latest. The decomposition and
split-subrepresentation conjuncts remain unproved; Task 5346 targets the whole
aggregate.

## Staged, not yet published

These candidates of Worker 1222 are staged for review. They are not Library
content; their proof tasks will be published only after integration.

- VI.7.2, second Lemma, printed p.182 / PDF p.188 (`R ⊣ I` for
  `Cusp(G) = ∏_P M(M)_sc`, exactness, faithfulness, preservation of finite type,
  injectivity of `V → IR(V)`): `BernsteinCuspAdjunctionStatement`, candidate
  `0715c8f1-1588-4789-ad1c-579785445921`.
- V.5.5, Proposition and Corollary, printed pp.127–128 / PDF pp.133–134
  (projection on a cone in a Euclidean space): `ConeProjectionStatements`,
  candidate `6fa78c15-c7bc-4a3f-9dca-a16546bb59cf`. It replaces candidate
  `6721ea5c-8134-4849-8e81-364c5e6a1596`, which Reviewer 269 rejected for a
  false explanatory claim in the empty-index case; the Lean statement is
  unchanged.
- VI.7.3, Proposition, printed p.185 / PDF p.191 (`i_P^G` maps `M(M)_𝔰` into
  `M(G)_{i_{MG}(𝔰)}`, and `r_P^G` maps `M(G)_𝔱` into
  `∏_{𝔰 ∈ i_{MG}^{-1}(𝔱)} M(M)_𝔰`): `BernsteinInductionRestrictionStatement`,
  candidate `18b7db44-be80-4ddc-b41b-bf40475eb00a`. The fibre
  `i_{MG}^{-1}(𝔱)` is expressed with cuspidal data of `G` contained in `M`,
  inner normalized induction in `M` and inertial equivalence in `G`; its
  Markdown explains why this is Renard's statement.
- VI.5.4, Theorem, printed pp.173–174 / PDF pp.179–180 (the bounds
  `length(i_P^G ρ) ≤ l(M)` and `dim Hom_G(π, π′) ≤ |W_M \ W(ρ, ρ′)|`, which the
  published `LeviSupercuspidalInductionAssociationStatement` leaves out):
  `BernsteinSupercuspidalInductionBoundsStatement`, candidate
  `c39d98dc-ef71-4cc5-9033-df02b3b38906`. It uses the published Weyl quotients
  `Weyl i` and `Group.RelativeWeyl.inclusion`.
- V.2.7, Corollary, printed p.109 / PDF p.115 (the orbits of the unramified
  characters in `Irr(G)` are complex algebraic tori):
  `RationalInertiaOrbitTorusStatement`, candidate
  `3516aaed-0418-4f68-9f2f-78b95b357460`, with the identifications of the
  Notations paragraph that follows the Corollary. The torus structure is
  stated through the published polynomial-function algebra
  `unramifiedRegularFunctions` on `X(G)`: its invariants under the stabilizer
  form a Laurent algebra in `rank Λ(G)` variables whose complex points are the
  points of the inertial class. It replaces candidate
  `1fdbdadf-eae5-456a-9aa8-33655023dfbf`, which Reviewer 627 rejected because
  it stated only a subgroup parametrization of the orbit and treated the
  Notations paragraph as notation only. The V.2.7 Lemma is the published and
  proved `RationalTwistStabilizerFiniteStatement`.

## Related tasks of other workers

- Worker 4169 published proof tasks for two Chapter V structural statements:
  Task 5309, `be989fac-448d-4a56-ad1b-663853caf8cd`
  (`AvailableRenardCartanStatement`, V.5.1 (4)–(5) and V.3.21–V.3.23), and
  Task 5310, `8d4643b8-dcf9-476e-a86f-04b62b8d738f`
  (`AvailableSimultaneousStandardBasisStatement`, V.3.23, V.5.1–V.5.2).
- The child programs of the previous update (Tasks 5296–5298) now have
  executors. On Task 5297 (III.3), Worker 151 reports three staged definition
  units and published the prerequisite Task 5338,
  `54fcba03-87f9-4b3a-ab99-618d2c683d74`, for the II.2.5 complex sheaf and
  test-module functors.
- The proof tasks 5279–5301 listed in the previous update have been claimed.
  Task 5301 (III.1.4) is done, with the published proof cited above; this
  note does not track the later status of the others.
  Task 5292 was retired after its executor followed its duplicate notice; the
  VI.10.4–VI.10.5 proof stays with `03c64afa-0ad5-47f5-a53e-2daac3536541`.

## Section findings

These findings update the previous note. Rows not mentioned keep their status
there.

- **I.3.** The remark after (I.3.2.1) on the two complex structures is now
  stated (above). With the units listed in the previous update, every
  positive assertion of I.3 that Worker 1222 identified has a published
  statement.
- **III.1.** III.1.4 and the III.1.15 assertions that the previous update
  listed as unstated are now stated (above). The III.1.4 equivalence is also
  proved (Worker 155's `heckeNondegenerateModuleEquivalence`, cited above);
  the III.1.15 unit is a statement only, with proof Task 5341 open. The
  III.1.15 unit contains its own smoothness and right-action statements; its
  relation to the earlier `RenardTensorHomStatements` is explained in its
  Markdown.
- **IV.** Worker 1222 audited Chapter IV against the Library. Published
  statements cover IV.1.1–IV.1.7, the IV.2.1 Definition and Remarks 1–2
  (`HermitianRepresentationStatements`), IV.2.2 and IV.3.2–IV.3.3, including
  the units above. The assertions of the IV.3.1 Definition (stability of
  `L²(G, χ, dg*)_0` under right translation and the invariant positive
  definite form) are realized by Worker 88's constructions with proofs in
  `Langlands.Representation.MatrixCoefficient.CentralL2`. Remaining gaps:
  - (IV.2.1.1)–(IV.2.1.2), printed p.97 / PDF p.103: normalized induction
    `i_H^G τ = ind_H^G(τ ⊗ δ_{H\G}^{1/2})` from an arbitrary closed subgroup
    `H` with compact `H \ G`, and `(i_H^G τ)~ = i_H^G(τ~)`,
    `(i_H^G τ)^h = i_H^G(τ^h)` for arbitrary smooth `τ`, are not stated.
    `HermitianRepresentationStatements` explicitly leaves them out. Two
    published results cover special cases only. The proved theorem
    `Induction.exists_integralDualEquiv_of_section` (module
    `Induction/CompactQuotientSmoothDuality`) gives the contragredient
    identity for a closed `P` with compact `P \ G`, a homomorphism
    `m : P → M` with a continuous section and representations inflated
    through `m`, under its explicit integral hypotheses.
    `Aubert/General/NormalizedInductionHermitianDuality` and
    `LeviInductionHermitianDualityStatement` (module
    `Exponents/MaximalLeviReducibilityUnitaryInputs`) give hermitian-dual
    consequences for admissible unitarizable representations under a
    semidirect decomposition.
  - IV.2.3 for a general cocompact closed subgroup `H` (only the Levi
    interface inputs are published).
  - The IV.3.1 remark on the Hilbert completion of `L²(G, χ)_0`, and the
    IV.3.3 remark on `G/A`.

  IV.3.4 consists of bibliographic notes.
- **V.2.** The V.2.7 Corollary is staged (above).
- **V.5.** V.5.5 is staged (above). The decomposition of `H(G, K)` in V.5.3
  (its Corollary, Theorem and Remark) is not stated. It needs the special
  compact and Cartan objects of the structural Chapter V interface (see
  [Chapter V structural inputs](chapter-v-structural-inputs.md)). The finite
  residual-coset mechanism of the V.5.3 proofs is implemented by internal
  supporting constructions (`FiniteResidualSandwich`,
  `ResidualIwahoriSandwich`, `ResidualCosetStabilization`); none of them
  states a V.5.3 assertion. V.5.4 is largely covered by other workers'
  publications, all in `Langlands.Representation.Aubert.General`:
  - the Proposition (unimodularity of `G(F)`) is
    `RationalReductiveUnimodularityStatement`, with the canonical point
    topology, the local-compactness, nonarchimedean-group and Hausdorff
    instance premises and the premise `StandardCocharacterStatement`. It is
    proved by `rationalReductiveUnimodularity`, whose Markdown records that
    the standard-cocharacter premise is not used and that the route avoids
    the Cartan and Iwahori decompositions of the source;
  - for the Lemma, `RationalParabolicModulusStatement` states unimodularity
    together with the identification of the modular character of a standard
    parabolic `P = M ⋉ U` with the Haar modulus of conjugation on `U`,
    conditional on `StandardCocharacterStatement` and retaining the canonical
    point topology, the local-compactness, nonarchimedean-group and Hausdorff
    instances, and the closedness and projection-continuity premises of the
    statement. It is proved by the published term
    `rationalParabolicModulus_of_reductiveUnimodularity
    rationalReductiveUnimodularity GroupScheme.dynamicCentralizerReductive`:
    the reduction (module `RationalLeviUnimodularityReduction`) applied to
    the proved unimodularity theorem and to the proved
    `Langlands.GroupScheme.dynamicCentralizerReductive`. The term occurs inside
    the published proof `rationalNaturalInductionDuality`
    (`RationalInductionDualityProof`, whose Markdown explains it); Worker 1222
    found no separately named theorem with this type.
    `RationalOppositeHaarReciprocityStatement` (the Haar
    characters of the standard and opposite radicals multiply to one on the
    Levi) is proved by `rationalOppositeHaarReciprocity`, and
    `DynamicUnipotentHaarDeterminantStatement` (Haar scaling on a dynamic
    unipotent subgroup is the normalized absolute value of the adjoint
    determinant on its Lie algebra) is proved by
    `dynamicUnipotentHaarDeterminant`. The comparison of that determinant
    with the root product `∏_{γ ∈ Σ(P)} |γ(a)|^{m_γ + 2m_{2γ}}` belongs to the
    `AdjointDeterminant*` statements of `Langlands.GroupScheme.Dynamic`, which
    this note does not map assertion by assertion.
- **VI.1.** VI.1.1 is stated for both normalizations: the normalized
  statements were already published; the unnormalized ones are above.
- **VI.5.** The two numerical bounds of the VI.5.4 Theorem are staged
  (above). The rest of VI.5.2–VI.5.4 is in the
  [supercuspidal induction map](supercuspidal-finite-length-progress.md).
- **VI.7.** The VI.7.2 Theorem, first Lemma and Proposition, and VI.7.4, are
  stated (above), and the abelian-block remark of VI.7.2 is proved (above);
  the VI.7.2 second Lemma and VI.7.3 are staged. The
  isomorphism (VI.7.2.1), `i_P^G(⊕_D W_D) ≃ ⊕_D i_P^G(W_D)`, is proved by
  Worker 1187's `Langlands.Representation.Aubert.General.InductionCoproducts`
  under an explicit compactness hypothesis on `P \ G`. Not stated: the VI.7.1
  variety structure of `Ω(G)` (Theorem) and the map `Sc` on isomorphism
  classes; and the remark of VI.7.4 that `e_𝔰` is not in `H(G)`. That remark
  is false in some cases: when `G(F)` is compact, and for `G = GL₁`, where the
  projector onto the block of the characters with a given restriction `χ₀` to
  `O^×` is the action of the compactly supported function
  `vol(O^×)⁻¹ χ₀⁻¹ 1_{O^×}`.
- **VI.9.** Worker 1222 found published statements for VI.9.4–VI.9.5
  (`RenardFamilyJacquetAdmissibilityStatement` and the
  `Jacquet/StandardFixedVector*` statements). This note does not map them
  assertion by assertion.
- **VI.10.** The VI.10.5 Proposition (Harish-Chandra homomorphisms) is
  published as Worker 6's `HarishChandraHomomorphismStatement`.
- **VII.1.** The VII.1.3 Corollary, listed as unstated in the ledger's
  section table, is published as
  `Langlands.Representation.Exponents.MaximalLeviBlockStatements`.
- **VII.3–VII.4.** The ledger's section table lists both as backlog; see the
  previous update for the published statements. The Proposition of VII.3.5
  remains unstated: the published VII.3.4 statement characterizes `J_{Q|P}`
  only through an arbitrary identification, while the composition laws of
  VII.3.5 need the operator normalized by the integral over `N̄ ∩ U`. Its
  hypotheses also need the distance `d(P, Q) = |Σ(P) ∩ Σ(Q̄)|` on reduced
  roots of `A_M`.
- **Chapter notes.** Worker 1222 read I.7, II.4, III.4, IV.3.4, VI.11 and
  VII.5. They consist of attributions and bibliographic comments. VI.11
  (printed p.218 / PDF p.224) also remarks, citing [2] and [3], that the
  second adjointness theorem is equivalent to a strong form of Casselman
  duality valid without admissibility. This equivalence is proved in the book
  itself: VI.9.6 (printed pp.201–202 / PDF pp.207–208) states second
  adjointness (VI.9.6.1) and the identity `r_{P̄}^G(π̃) ≃ (r_P^G π)~` for every
  smooth `π` (VI.9.6.2), proves their equivalence (through the Hom chain
  (VI.9.6.3), smooth-bidual embeddings and A.III.3), and then reformulates
  (VI.9.6.2) through the Casselman pairing (VI.9.6.4)–(VI.9.6.5). The two
  theorems are published as the separate statements
  `LeviSecondAdjointnessStatement` and `LeviJacquetContragredientStatement`
  (represented-parabolic interface, `Langlands.Representation.Exponents`;
  their status is in the
  [parabolic-functor map](parabolic-functors-tempered-progress.md)). Worker
  1222 found no published declaration stating their equivalence: that
  in-book derivation remains a formalization obligation of this task.

## Remaining work recorded here

The ledger's section table still predates both updates and should be
rewritten from them and from the child programs' source maps. Open statement
gaps named above: I.2.3 (unital right adjoint and final Remark), the I.2.1
caveat (e), (IV.2.1.1)–(IV.2.1.2) and IV.2.3 for general cocompact `H`, the
IV.3.1 and IV.3.3 remarks, the V.5.3 decomposition of `H(G, K)`, the VI.7.1
Theorem and `Sc`, the equivalence of (VI.9.6.1) and (VI.9.6.2), and VII.3.5. The VI.4 map
lists further unstated internal assertions of VI.4.1–VI.4.4. Apart from
III.1.4 and the abelian-block conjunct of the VI.7.2 Theorem unit, which are
proved, the statement units above still need proofs; their proof tasks are
listed in the tables, and the staged units will receive theirs after
integration.
