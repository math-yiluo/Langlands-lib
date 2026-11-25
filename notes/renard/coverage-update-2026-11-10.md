# Renard 2026: coverage update, 10 November 2026

This note continues the
[coverage update of 9 November 2026](coverage-update-2026-11-09.md) and the
[whole-book ledger](coverage.md). It records the statement modules that entered
the Library between that update and 10 November 2026, related statements
elsewhere in the Library, and audit findings. It declares no section, chapter or book complete.
A published statement is not a proof; every row keeps the proof status
explicit.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF page numbers equal printed page numbers plus six. Library facts refer to
commit `45606b6bf1145d8d8b4633e8eb97477209c366b7`, except the column and
parentheses that give the proofs the Library has now.

## New statement publications

Each module below is a statement module of the Library.
The III.1.4 statement is proved, and so is one conjunct of the VI.7.2 Theorem
module (the blocks are abelian); see below the table. For the other seven
propositions, and for the remaining conjuncts of the VI.7.2 Theorem module,
the Library had no theorem or published proof term of their types at the
commit above: their names occurred only in their own statement files (and,
for the abelian conjunct, in its proof). The last column gives the proof the
Library has now.

| Source assertion | Library module and entry declaration | Proof in the Library |
| --- | --- | --- |
| I.3.2, remark after (I.3.2.1), printed p.20 / PDF p.26: the complex structures on `A ⊗_{eAe} Z` from `A` and from `Z` coincide | `Langlands.Algebra.NonUnitalModuleCornerInductionComplexScalarsStatement`, `Langlands.Algebra.NonUnitalModuleCornerInduction.ComplexScalarsStatement` | proved: `complexScalarsStatement` (`Langlands/Algebra/NonUnitalModuleCornerInductionComplexScalarsProof.lean`) |
| III.1.4, Theorem, printed p.60 / PDF p.66: smooth representations are equivalent to nondegenerate `H(G)`-modules | `Langlands.Representation.Hecke.NondegenerateModuleEquivalenceStatement` | proved: `Langlands.Hecke.heckeNondegenerateModuleEquivalence` (below) |
| III.1.14–III.1.15, printed pp.66–69 / PDF pp.72–75: smoothness of tensor products, the right `H(G)`-action by `π(Ť)`, `(V₁ ⊗ V₂)_G ≅ V₁ ⊗_{H(G)} V₂`, (III.1.15.1), and Remark 3 (twists) | `Langlands.Representation.Smooth.RenardCoinvariantTensorStatements`, `Langlands.Renard.Smooth.RenardCoinvariantTensorStatements` | proved: `renardCoinvariantTensorStatements` (`Langlands/Representation/Smooth/RenardCoinvariantTensorProof.lean`) |
| IV.1.1, multiplicity formula, printed p.89 / PDF p.95; IV.3.3, Corollary, last sentence, printed p.102 / PDF p.108 | `Langlands.Representation.Compact.CompactMultiplicityIndependenceStatements`, `Langlands.Renard.CompactRepresentation.CompactMultiplicityIndependenceStatements` | proved: `compactMultiplicityIndependence` (`Langlands/Representation/Compact/CompactMultiplicityIndependenceProof.lean`) |
| IV.1.6–IV.1.7, printed pp.94–95 / PDF pp.100–101: compact irreducibles are projective and injective, `M(G)_c` is semisimple, and the three block decompositions | `Langlands.Representation.Compact.CompactBlockDecompositionStatements`, `Langlands.Renard.CompactRepresentation.CompactBlockDecompositionStatements` | proved: `compactBlockDecomposition` (`Langlands/Representation/Compact/CompactBlockDecompositionProof.lean`) |
| VI.1.1, printed pp.134–135 / PDF pp.140–141: Frobenius reciprocity, exactness and limits for the unnormalized functors `Ind_P^G` and `j_N` | `Langlands.Representation.Exponents.LeviUnnormalizedParabolicStatements`, `Langlands.Aubert.General.RepresentedParabolic.LeviUnnormalizedParabolicStatements` | proved: `leviUnnormalizedParabolicStatements` (`Langlands/Representation/Exponents/LeviUnnormalizedParabolicProof.lean`) |
| VI.7.2, Theorem, (VI.7.2.2)–(VI.7.2.3), first Lemma and the remark that blocks are abelian, printed pp.181–184 / PDF pp.187–190 | `Langlands.Representation.CuspidalSupport.BernsteinDecompositionStatements`, `Langlands.CuspidalSupport.BernsteinDecompositionStatements` | not proved; derived from further hypotheses by `bernsteinDecompositionStatements_of_inputs` (`Langlands/Representation/CuspidalSupport/BernsteinDecompositionStatementsFromInputs.lean`) |
| VI.7.2, Proposition, printed p.184 / PDF p.190: three characterizations of a Bernstein block (embedding in, or subquotient of, a sum of `i_P^G(τ)` with `τ ∈ M(M)_D`; vanishing of the non-conjugate Jacquet components) | `Langlands.Representation.CuspidalSupport.BernsteinBlockCharacterizationStatement`, `Langlands.CuspidalSupport.BernsteinBlockCharacterizationStatement` | not proved; derived from further hypotheses by `bernsteinBlockCharacterization_of_leviInputs` (`Langlands/Representation/CuspidalSupport/BernsteinFixedLeviEmbeddingReduction.lean`) |
| VI.7.4, printed pp.185–186 / PDF pp.191–192: central idempotents `e_𝔰` and the decomposition of `H(G)` into the ideals `S_𝔰` | `Langlands.Representation.CuspidalSupport.BernsteinCentralIdempotentStatements`, `Langlands.CuspidalSupport.BernsteinCentralIdempotentStatements` | not proved; derived from further hypotheses by `bernsteinCentralIdempotentStatements_of_decomposition` (`Langlands/Representation/CuspidalSupport/BernsteinHeckeIdealReduction.lean`) |

The entry declaration of the III.1.4 module is
`Langlands.Hecke.HeckeNondegenerateModuleEquivalenceStatement`. It is proved:
the theorem `Langlands.Hecke.heckeNondegenerateModuleEquivalence`
(module `Langlands.Representation.Hecke.NondegenerateModuleEquivalenceProof`)
has exactly the type `HeckeNondegenerateModuleEquivalenceStatement.{u, v}`.
It first appeared in the Library at commit
`e449cde988d4e97ab280b8d4d11262887ccc26e0`.

The VI.7.2 Theorem module `BernsteinDecompositionStatements` is the conjunction
of three statements. Its conjunct `BernsteinBlockAbelianStatement` (every
block is abelian with the inherited preadditive structure) is proved by
the theorem `Langlands.CuspidalSupport.bernsteinBlockAbelian` (module
`Langlands.Representation.CuspidalSupport.BernsteinBlockAbelianProof`), in the
Library since commit `e449cde988d4e97ab280b8d4d11262887ccc26e0` at the latest.
The decomposition and split-subrepresentation conjuncts were unproved at the
commit above; for the whole aggregate see the table.

## Stated after the commit above

These statements were not in the Library at the commit above; they entered it
later, and the [coverage update of 11 November 2026](coverage-update-2026-11-11.md)
gives their modules and their proofs.

- VI.7.2, second Lemma, printed p.182 / PDF p.188 (`R ⊣ I` for
  `Cusp(G) = ∏_P M(M)_sc`, exactness, faithfulness, preservation of finite type,
  injectivity of `V → IR(V)`): `BernsteinCuspAdjunctionStatement`.
- V.5.5, Proposition and Corollary, printed pp.127–128 / PDF pp.133–134
  (projection on a cone in a Euclidean space): `ConeProjectionStatements`.
- VI.7.3, Proposition, printed p.185 / PDF p.191 (`i_P^G` maps `M(M)_𝔰` into
  `M(G)_{i_{MG}(𝔰)}`, and `r_P^G` maps `M(G)_𝔱` into
  `∏_{𝔰 ∈ i_{MG}^{-1}(𝔱)} M(M)_𝔰`): `BernsteinInductionRestrictionStatement`.
  The fibre
  `i_{MG}^{-1}(𝔱)` is expressed with cuspidal data of `G` contained in `M`,
  inner normalized induction in `M` and inertial equivalence in `G`; its
  Markdown explains why this is Renard's statement.
- VI.5.4, Theorem, printed pp.173–174 / PDF pp.179–180 (the bounds
  `length(i_P^G ρ) ≤ l(M)` and `dim Hom_G(π, π′) ≤ |W_M \ W(ρ, ρ′)|`, which the
  published `LeviSupercuspidalInductionAssociationStatement` leaves out):
  `BernsteinSupercuspidalInductionBoundsStatement`. It uses the published Weyl quotients
  `Weyl i` and `Group.RelativeWeyl.inclusion`.
- V.2.7, Corollary, printed p.109 / PDF p.115 (the orbits of the unramified
  characters in `Irr(G)` are complex algebraic tori):
  `RationalInertiaOrbitTorusStatement`, with the identifications of the
  Notations paragraph that follows the Corollary. The torus structure is
  stated through the published polynomial-function algebra
  `unramifiedRegularFunctions` on `X(G)`: its invariants under the stabilizer
  form a Laurent algebra in `rank Λ(G)` variables whose complex points are the
  points of the inertial class. A subgroup parametrization of the orbit alone
  would not state the Corollary, and the Notations paragraph is part of the
  assertion, not notation only. The V.2.7 Lemma is the published and
  proved `RationalTwistStabilizerFiniteStatement`.

## Related statements

- Two Chapter V structural statements: `AvailableRenardCartanStatement`
  (V.5.1 (4)–(5) and V.3.21–V.3.23) and
  `AvailableSimultaneousStandardBasisStatement` (V.3.23, V.5.1–V.5.2);
  the second is proved, as `availableSimultaneousStandardBasis`
  (`Langlands/BruhatTits/SpecialCompact/AvailableBasisProof.lean`); the first
  is not proved (it is a hypothesis of
  `jointSpecialCompactBasisExistence_of_remainingInputs`,
  `Langlands/BruhatTits/SpecialCompact/JointBasisFinalAssembly.lean`).
- The gaps of the previous update have their own source maps
  ([III.2](iii2-hecke-induction.md), [III.3](iii3-sheaf-sections.md),
  [II.3](ii3-td-groups.md)). III.3 uses the II.2.5 complex sheaf and
  test-module functors.
- The previous update gives the present proofs of its statements in its
  tables.

## Section findings

These findings update the previous note. Rows not mentioned keep their status
there.

- **I.3.** The remark after (I.3.2.1) on the two complex structures is now
  stated (above). With the modules listed in the previous update, every
  positive assertion of I.3 that this audit identified has a published
  statement.
- **III.1.** III.1.4 and the III.1.15 assertions that the previous update
  listed as unstated are now stated (above). The III.1.4 equivalence is also
  proved (`heckeNondegenerateModuleEquivalence`, cited above);
  the III.1.15 module was a statement only at the commit above (for its proof
  now see the table). The
  III.1.15 module contains its own smoothness and right-action statements; its
  relation to the earlier `RenardTensorHomStatements` is explained in its
  Markdown.
- **IV.** Chapter IV was audited against the Library. Published
  statements cover IV.1.1–IV.1.7, the IV.2.1 Definition and Remarks 1–2
  (`HermitianRepresentationStatements`), IV.2.2 and IV.3.2–IV.3.3, including
  the modules above. The assertions of the IV.3.1 Definition (stability of
  `L²(G, χ, dg*)_0` under right translation and the invariant positive
  definite form) are realized by constructions with proofs in
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
- **V.2.** The V.2.7 Corollary was stated after the commit above (above).
- **V.5.** V.5.5 was stated after the commit above (above). The decomposition of `H(G, K)` in V.5.3
  (its Corollary, Theorem and Remark) is not stated. It needs the special
  compact and Cartan objects of the structural Chapter V interface (see
  [Chapter V structural inputs](chapter-v-structural-inputs.md)). The finite
  residual-coset mechanism of the V.5.3 proofs is implemented by internal
  supporting constructions (`FiniteResidualSandwich`,
  `ResidualIwahoriSandwich`, `ResidualCosetStabilization`); none of them
  states a V.5.3 assertion. V.5.4 is largely covered by statements elsewhere
  in the Library, all in `Langlands.Representation.Aubert.General`:
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
    (`RationalInductionDualityProof`, whose Markdown explains it); no
    separately named theorem with this type was found.
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
- **VI.5.** The two numerical bounds of the VI.5.4 Theorem were stated after
  the commit above (above). The rest of VI.5.2–VI.5.4 is in the
  [supercuspidal induction map](supercuspidal-finite-length-progress.md).
- **VI.7.** The VI.7.2 Theorem, first Lemma and Proposition, and VI.7.4, are
  stated (above), and the abelian-block remark of VI.7.2 is proved (above);
  the VI.7.2 second Lemma and VI.7.3 were stated after the commit above. The
  isomorphism (VI.7.2.1), `i_P^G(⊕_D W_D) ≃ ⊕_D i_P^G(W_D)`, is proved by
  `Langlands.Representation.Aubert.General.InductionCoproducts`
  under an explicit compactness hypothesis on `P \ G`. Not stated: the VI.7.1
  variety structure of `Ω(G)` (Theorem) and the map `Sc` on isomorphism
  classes; and the remark of VI.7.4 that `e_𝔰` is not in `H(G)`. That remark
  is false in some cases: when `G(F)` is compact, and for `G = GL₁`, where the
  projector onto the block of the characters with a given restriction `χ₀` to
  `O^×` is the action of the compactly supported function
  `vol(O^×)⁻¹ χ₀⁻¹ 1_{O^×}`.
- **VI.9.** There are published statements for VI.9.4–VI.9.5
  (`RenardFamilyJacquetAdmissibilityStatement` and the
  `Jacquet/StandardFixedVector*` statements). This note does not map them
  assertion by assertion.
- **VI.10.** The VI.10.5 Proposition (Harish-Chandra homomorphisms) is
  published as `HarishChandraHomomorphismStatement`.
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
- **Chapter notes.** I.7, II.4, III.4, IV.3.4, VI.11 and VII.5 were read.
  They consist of attributions and bibliographic comments. VI.11
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
  [parabolic-functor map](parabolic-functors-tempered-progress.md)). No
  published declaration stated their equivalence at the commit above; it was
  stated later, as
  `LeviSecondAdjointnessContragredientEquivalenceStatement` (see the
  [coverage update of 11 November 2026](coverage-update-2026-11-11.md)).

## Remaining work recorded here

The ledger's section table still predates both updates and should be
rewritten from them and from the source maps of III.2, III.3 and II.3. Open statement
gaps named above: I.2.3 (unital right adjoint and final Remark), the I.2.1
caveat (e), (IV.2.1.1)–(IV.2.1.2) and IV.2.3 for general cocompact `H`, the
IV.3.1 and IV.3.3 remarks, the V.5.3 decomposition of `H(G, K)`, the VI.7.1
Theorem and `Sc`, the equivalence of (VI.9.6.1) and (VI.9.6.2), and VII.3.5. The VI.4 map
lists further unstated internal assertions of VI.4.1–VI.4.4. Apart from
III.1.4 and the abelian-block conjunct of the VI.7.2 Theorem module, which are
proved, the statement modules above had no proofs at the commit above; the
table gives their present proofs.
