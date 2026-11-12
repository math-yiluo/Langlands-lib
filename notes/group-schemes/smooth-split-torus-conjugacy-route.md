# Group schemes: unconditional rational lifting and maximal split torus conjugacy

Author: Worker 15, 8 November 2026, for the algebraic and reductive group-scheme
program `2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483).

This note records compile-checked proof routes from published Library results, at
commit `c4a16df784376405a45b60df82583e8c26d8a4e3`, to the following targets:

- `SmoothMaximalSplitTorusConjugacyStatement`. This is Borel–Tits conjugacy of maximal
  split tori in smooth connected affine groups over every field, as in Conrad–Gabber–Prasad
  (CGP), *Pseudo-reductive groups*, second edition, Theorem C.2.3.
- `PseudoParabolicQuotientRationalLiftingStatement`, which is CGP Lemma C.2.1.
- Sixteen further published targets that follow from these two. Some of them also need
  the `ParabolicDynamicStatement` route recorded in
  [the composable-targets note](composable-targets-2026-11-08.md).

These are development checks, not proof publications. Each target still needs an accepted
`lean.proof@1` candidate from its proof task. The tables below name those tasks.

## Evidence

All terms below were compiled with `lean_check` in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, in a private draft of the author's workspace.
The compilation had no errors. For each final theorem, the inspection reported only the
axioms `propext`, `Classical.choice` and `Quot.sound`. Independent proof review is still
required.

## The observation: normality is needed only over infinite fields

`SmoothMaximalSplitTorusConjugacyStatement` appears about eighty times as a hypothesis
in the published Library, in group-scheme and representation-theory modules. Its
published reductions
(`smoothMaximalSplitTorusConjugacy_of_solvable_of_envelope_of_structure_of_containment`,
`splitTorusIntoPseudoParabolic_of_components` and
`PseudoParabolicRationalLiftingAssembly.statement_of_structural_inputs`) take only proved
inputs, with one exception. That exception is `TorusGeneratedEnvelopeNormalityStatement`
(CGP Proposition A.2.11, all fields; task `a7bfc3ed-d470-4798-ad99-524ea48c92d8`), which
is still open.

The assembly uses that statement only once. The call is in
`PseudoParabolicRationalLiftingAssembly.property_of_trivial_split_radical`, which assumes
`[Infinite k]`. Over an infinite field, normality already follows from two published
results:

- `TorusGeneratedEnvelope.isNormal_of_algebraicClosure_envelope_eq` (module
  `Rational.TorusGeneratedEnvelopeNormalityReduction`) derives normality of the envelope
  from its compatibility with the algebraic closure.
- `torusGeneratedEnvelopeAlgebraicClosureInfinite_of maximalTorusBaseChange
  maximalTorusConjugacy rationalMaximalTorusConjugateDensity` proves that compatibility
  over every infinite field (module
  `Rational.TorusGeneratedEnvelopeAlgebraicClosureInfiniteReduction`).

The route below therefore repeats the short body of `property_of_trivial_split_radical`,
supplying infinite-field normality as a proved lemma. The finite-field branch is the
published `property_of_finite`. Task `a7bfc3ed` remains a genuine target, because its
statement covers finite fields, but these consequences do not depend on it.

## Lean text

Names are in `Langlands.GroupScheme` unless written in full. The proof sits under
`noncomputable section` with `open CategoryTheory AlgebraicGeometry`.

```lean
theorem envelope_isNormal_of_infinite {k : Type u} [Field k] [Infinite k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (D : TorusGeneratedEnvelope G) : (SubgroupFunctor.range D.inclusion).IsNormal :=
  D.isNormal_of_algebraicClosure_envelope_eq
    (torusGeneratedEnvelopeAlgebraicClosureInfinite_of maximalTorusBaseChange
      maximalTorusConjugacy rationalMaximalTorusConjugateDensity k G)

theorem property_of_trivial_split_radical {k : Type u} [Field k] [Infinite k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {N : GroupScheme (Spec (CommRingCat.of k))} (n : N ⟶ G)
    (hn : IsSplitUnipotentRadical n) (hzero : SubgroupFunctor.range n = ⊥) :
    PseudoParabolicRationalLiftingProperty G := by
  obtain ⟨D, hsmD, -, -⟩ := exists_pointed_torusDominated_envelope G
  let : Smooth D.group.X.hom := hsmD
  intro P i hi Q q hsep hlft hqc hsmq hsurjq hqcq hfib x
  let : IsSeparated Q.hom := hsep
  let : LocallyOfFiniteType Q.hom := hlft
  let : QuasiCompact Q.hom := hqc
  let : Smooth q.left := hsmq
  let : Surjective q.left := hsurjq
  let : QuasiCompact q.left := hqcq
  let E := DynamicParabolicPresentation.ofSplitProduct hi n hzero
    (fun U j hj χ T a => pseudoParabolicSplitRadicalProduct k G U N j n hj hn χ T a)
  exact D.rational_lifts_dynamic (envelope_isNormal_of_infinite G D)
    (torusGeneratedEnvelopeRationalDensity k G D)
    i hi.isClosedSubgroup E.cocharacter E.range_eq q hfib x

theorem rationalLifting : PseudoParabolicQuotientRationalLiftingStatement.{u} := by
  apply PseudoParabolicSplitRadicalInduction.statement_of_trivial_split_radical
    SplitUnipotentRadicalExistence.splitUnipotentRadicalExistence normalSubgroupQuotient
    splitUnipotentAffineTorsorStatement pseudoParabolicSplitRadicalQuotient
  intro k _ G _ _ _ N n hn hzero
  obtain hfinite | hinfinite := finite_or_infinite k
  · let : Finite k := hfinite
    exact PseudoParabolicRationalLiftingAssembly.property_of_finite G
  · let : Infinite k := hinfinite
    exact property_of_trivial_split_radical G n hn hzero

theorem smoothMaximalSplitTorusConjugacy : SmoothMaximalSplitTorusConjugacyStatement.{u} :=
  smoothMaximalSplitTorusConjugacy_of_solvable_of_envelope_of_structure_of_containment
    solvableMaximalSplitTorusConjugacy noProperPseudoParabolicSolvableEnvelope
    pseudoParabolicSubgroupStructure
    (splitTorusIntoPseudoParabolic_of_components smoothSubgroupQuotientExistence
      pseudoParabolicSubgroupStructure pseudoParabolicQuotientPseudoComplete
      splitSolvablePseudoCompleteFixedPoint rationalLifting)
```

These declarations import the following `Langlands.GroupScheme` modules:
`Rational.MaximalSplitTorusDescentReduction`,
`Rational.SolvableMaximalSplitTorusConjugacyProof`,
`Rational.NoProperPseudoParabolicSolvableEnvelopeProof`, `PseudoParabolicStructureProof`,
`SplitTorusIntoPseudoParabolicReduction`, `HomogeneousQuotientProof`,
`PseudoParabolicQuotientPseudoCompleteAssembly`, `SplitSolvableFixedPointProof`,
`PseudoParabolicRationalLiftingAssembly`, `Reductive.SplitUnipotentRadicalExistenceProof`,
`NormalSubgroupQuotientProof`, `SplitUnipotentAffineTorsorProof`,
`PseudoParabolicSplitRadicalProductProof`, `PseudoParabolicSplitRadicalQuotientProof`,
`Rational.TorusGeneratedEnvelopeRationalDensityProof`,
`Rational.TorusGeneratedEnvelopeNormalityReduction`,
`Rational.TorusGeneratedEnvelopeAlgebraicClosureInfiniteReduction`,
`Torus.MaximalBaseChangeProof`, `Absolute.MaximalTorusConjugacyProof` and
`Rational.RationalMaximalTorusDensityProof`.

## Consequences

`SC` denotes `smoothMaximalSplitTorusConjugacy` and `RL` denotes `rationalLifting`.
`PD` is the `ParabolicDynamicStatement` proof from the composable-targets note
(task `42c85926-0d43-4d0d-abef-f3350c4273ae`). `QC` abbreviates the four arguments
`smoothSubgroupQuotientExistence pseudoParabolicSubgroupStructure
pseudoParabolicQuotientPseudoComplete splitSolvablePseudoCompleteFixedPoint`.

### Targets that do not use `PD`

| Target | Composite term | Proof task |
| --- | --- | --- |
| `PseudoParabolicQuotientRationalLiftingStatement` (CGP C.2.1) | `RL` above | `56937d3d-4afc-4779-b7bb-f778da8a94c7` |
| `SmoothMaximalSplitTorusConjugacyStatement` (CGP C.2.3) | `SC` above | `7c6d89b9-d59a-44ce-aac6-95f9fafe7b82` |
| `SplitSolvableIntoPseudoParabolicStatement` (CGP C.2.2) | `splitSolvableIntoPseudoParabolic_of_components QC RL` | `7d0bdfab-7115-413c-8b81-84b633a697e4` |
| `SplitTorusIntoPseudoParabolicStatement` | `splitTorusIntoPseudoParabolic_of_components QC RL` | `bcbcd5f3-51b9-464a-b2bf-009c916d964f` |
| `SmoothMaximalSplitTorusDescentStatement` | `smoothMaximalSplitTorusDescent_of_envelope_of_structure_of_containment noProperPseudoParabolicSolvableEnvelope pseudoParabolicSubgroupStructure (previous row)` | none found |
| `DerivedMaximalSplitTorusStatement` | `derivedMaximalSplitTorus_of_smoothMaximalSplitTorusConjugacy SC` | `45bba50f-b29d-49c2-b923-64037208e2e1` |
| `SimplyConnectedDerivedCoverSplitTorusStatement` | `simplyConnectedDerivedCoverSplitTorusStatement_of_inputs (previous row) simplyConnectedCoverSplitTorus splitTorusIsogenyCocharacter` | `d2eaa936-79f4-4239-a7df-6f278e3549c3` |
| `MinimalParabolicSplitTorusConjugacyStatement` | `minimalParabolicSplitTorusConjugacy_of_smoothConjugacy SC` | `5b611ce8-28f2-4a58-a11d-dc455c208d9a` |
| `MaximalSplitTorusConjugacyStatement` (reductive groups, conjugacy and split rank) | hand-written, below | `6cba93f0-40f3-481b-8d85-76977bc6e4ef` |
| `PseudoParabolicMaximalSplitTorusStructureStatement` (CGP C.2.4) | hand-written, below | `592f15fa-989c-4d40-8529-fac851dbc1c5` |
| `MinimalPseudoParabolicConjugacyStatement` (CGP C.2.5) | `minimalPseudoParabolicConjugacy_of_structure pseudoParabolicSubgroupStructure SplitUnipotentRadicalExistence.splitUnipotentRadicalExistence pseudoParabolicSplitSolvableEnvelope (C.2.2 row) (C.2.4 row)` | `47af2faf-f36e-41b0-9590-1eaeeb374639` |

### Targets that also use `PD`

| Target | Composite term | Proof task |
| --- | --- | --- |
| `MinimalParabolicConjugacyStatement` (Borel–Tits 4.13) | `minimalParabolicConjugacyStatement_of_pseudoParabolic PD (fun _ _ _ hG => hG.hasTrivialUnipotentRadical) (C.2.5 row)` | `85b598ca-aba7-4d05-b7f3-249464d45ee6` |
| `GenericMinimalParabolicStatement` | hand-written, below | `bc8072c0-8a2b-4636-ab3c-7f04a4afb6a5` |
| `ParabolicSplitTorusLeviConjugacyStatement` | `parabolicSplitTorusLeviConjugacyStatement_of_dynamic_and_smoothConjugacy PD SC` | none found |
| `DynamicLeviParabolicCorrespondenceStatement` | `dynamicLeviParabolicCorrespondenceStatement_of_structural_statements PD dynamicCentralizerReductive dynamicLeviCocharacterRealization SC dynamicConnected relativeRootSignInclusions relativeRootNegation` | `d3b6c242-33dc-4a7c-b1f5-fdc94e7d576e` |
| `ParabolicRootPresentationExistenceStatement` | `parabolicRootPresentationExistenceStatement_of_dynamic_centralizer (GenericMinimalParabolic row) relativeRootNegation PD dynamicCentralizerReductive` | a component of `c6c736b5-f1c4-4203-bb23-f7981c4fc3af` |
| `ParabolicRootPresentationStatement` | `parabolicRootPresentationStatement_of_existence_of_reflections (previous row) (relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization)` | `c6c736b5-f1c4-4203-bb23-f7981c4fc3af` |
| `RelativeWeylGroupRestrictStatement` | `relativeWeylGroupRestrictStatement_of_structuralInputs ⟨(GenericMinimalParabolic row), (MinimalParabolicConjugacy row), (MinimalParabolicSplitTorusConjugacy row), genericCentralizer, parabolicSelfNormalizerStatement_of_rational_descent borelConjugacy borelNormalizer PD dynamicConnected⟩` | `2a35f486-8548-4812-b9bf-201edcc602fe` |

### Hand-written steps

These proofs follow the declarations above in the same namespace. The private check used
the same bodies, under other declaration names. They additionally import
`Derived.MaximalSplitTorusConjugacyReduction`, `Rational.MinimalParabolicAssembly`,
`Rational.MaximalSplitTorusExtension`, `Rational.GenericMinimalParabolicReduction`,
`Rational.ParabolicFunctorCocharacter`, `Rational.CocharacterMaximalSplitTorusProof`,
`Dynamic.SmoothProof`, `Dynamic.ConnectedProof`, `Rational.RelativeRootSignInclusionsProof`,
`Rational.RelativeRootNegationProof`,
`Rational.PseudoParabolicMaximalSplitTorusStructureReduction`,
`Rational.PseudoParabolicMinimalityCriterionReduction`,
`Rational.MinimalPseudoParabolicCentralizerProduct`,
`Rational.PseudoParabolicSplitSolvableEnvelopeProof` and
`PseudoParabolicSplitRadicalContainmentProof`.

```lean
theorem maximalSplitTorusConjugacy : MaximalSplitTorusConjugacyStatement.{u} := by
  apply maximalSplitTorusConjugacyStatement_of_extension_conjugacy
  · intro k _ G hG J _ j hj
    have : IsAffineHom G.X.hom := hG.isAffineHom
    have : Smooth G.X.hom := hG.smooth
    have : LocallyOfFiniteType G.X.hom := inferInstance
    exact exists_maximalSplitTorus_extension G (T := splitTorus.commGroupScheme _ J) j
      ⟨isSplitTorus_splitTorus J, hj⟩
  · intro k _ G hG
    have : Smooth G.X.hom := hG.smooth
    have : IsAffineHom G.X.hom := hG.isAffineHom
    have : ConnectedSpace G.X.left := hG.connectedSpace
    exact smoothMaximalSplitTorusConjugacy k G

theorem genericMinimalParabolic : GenericMinimalParabolicStatement.{u} := by
  intro k _ G hG T i hi ν
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro hν
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := CommGroupScheme.groupHom ν ≫ i
  let P := Dynamic.Affine.parabolicScheme χ
  let j := Dynamic.Affine.parabolicHom χ
  have hj : (Dynamic.parabolic χ).IsRepresentedBy j := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hjc : IsClosedSubgroup j := Dynamic.Affine.isClosedSubgroup_parabolicHom χ
  have : Smooth P.X.hom := (dynamicSmooth k G χ P j).1 hj
  have : ConnectedSpace P.X.left := ((dynamicConnected k G χ P j).2 inferInstance).1 hj
  refine ⟨⟨P, j, isParabolicSubgroup_of_range_eq_dynamicParabolic hG j hjc χ hj.2, hj.2⟩, ?_⟩
  intro F' hF' hle
  obtain ⟨ψ, hψ⟩ := hF'.exists_dynamicCocharacter parabolicDynamic hG
  subst hψ
  exact generic_dynamicParabolic_eq_of_le_of_structural cocharacterMaximalSplitTorus
    smoothMaximalSplitTorusConjugacy relativeRootSignInclusions relativeRootNegation
    k G hG T i hi ν P j hjc hj hν ψ hle

theorem pseudoParabolicMaximalSplitTorusStructure :
    PseudoParabolicMaximalSplitTorusStructureStatement.{u} := by
  intro k _ G P _ _ _ i hi S s hs
  obtain ⟨h1, h2⟩ := pseudoParabolicTorusCentralizerContainment_of_conjugacy
    smoothMaximalSplitTorusConjugacy k G P i hi S s hs
  refine ⟨h1, h2, fun U j hj => ⟨fun hmin => ?_, fun hprod => ?_⟩⟩
  · exact pseudoParabolicCentralizerProductOfMinimality_of_statements
      smoothMaximalSplitTorusConjugacy pseudoParabolicSplitRadicalProduct
      pseudoParabolicSplitRadicalContainment k G P i hi S s hs U j hj hmin
  · exact pseudoParabolicMinimalityOfCentralizerProduct_of_statements
      smoothMaximalSplitTorusConjugacy pseudoParabolicSplitSolvableEnvelope
      (splitSolvableIntoPseudoParabolic_of_components smoothSubgroupQuotientExistence
        pseudoParabolicSubgroupStructure pseudoParabolicQuotientPseudoComplete
        splitSolvablePseudoCompleteFixedPoint rationalLifting)
      k G P i hi S s hs U j hj hprod
```

In `maximalSplitTorusConjugacy`, the first goal is the extension of every closed split
torus to a maximal split torus. The published `exists_maximalSplitTorus_extension` gives
it, for any affine group locally of finite type. The second goal is the conjugacy
clause, which `SC` gives. The split-rank clause then follows inside the published
`maximalSplitTorusConjugacyStatement_of_extension_conjugacy`.

In `genericMinimalParabolic`, the representative of `P(ν ≫ i)` is the published closed
`Dynamic.Affine.parabolicHom`. It is parabolic by the (⇐) direction of Milne 25.1, the
published `isParabolicSubgroup_of_range_eq_dynamicParabolic`. A smaller parabolic functor
is `P(ψ)` for a cocharacter `ψ` over `k`, by `PD`. The published reduction
`generic_dynamicParabolic_eq_of_le_of_structural` then gives equality.

## Effect on the earlier note and remaining blockers

The [composable-targets note](composable-targets-2026-11-08.md) listed
`SmoothMaximalSplitTorusConjugacyStatement` and `GenericMinimalParabolicStatement` as
open blockers. Both now have routes. The fixpoint over published reductions was rerun
with all the targets above treated as proved. It found no further closures, apart from
the near misses already listed in that note.

The next blocker on the rational Bruhat path is `ParabolicIntersectionCentralizerStatement`
(Borel–Tits, *Groupes réductifs* (1965), 4.18; task
`233d5de4-ab94-42d3-a152-568bc2798f69`). It asserts that two rational parabolics contain
the centralizer of a common maximal split torus. Its published consumers then close:

- `RationalBruhatStatement`, through
  `rationalBruhatStatement_of_centralizer_and_parabolic_inputs genericCentralizer
  (GenericMinimalParabolic row) hCommon (MinimalParabolicSplitTorusConjugacy row)` (module
  `Rational.BruhatOpenCellProof`);
- `RelativeTitsSystemStatement`, through
  `relativeTitsSystemStatement_of_bruhat_and_rankOneFactorization`;
- `RepresentedParabolicDoubleCosetStatement`, through
  `representedParabolicDoubleCosetStatement_of_dynamic_structural_inputs`.

No published reduction yields 4.18 from proved inputs. A possible proof route, not
checked in Lean, has four steps:

1. Shrink both parabolics to minimal ones, using the published
   `parabolicContainsMinimalStatement`.
2. Show that for a minimal `P` the intersection `P ∩ Q` maps onto `P / R_u(P)`, because
   that Levi quotient has no proper rational parabolic.
3. Show that a maximal split torus of `P ∩ Q` therefore has the split rank of `G`.
4. Apply the second clause of the C.2.4 row to both `P` and `Q`.

Step 2 needs the two-parabolic geometry (`ParabolicIntersectionGeometryStatement`).
Its published reduction `parabolicIntersectionGeometry_of_commonTorus` still requires a
common maximal torus over the algebraic closure.
`StandardParabolicClassificationStatement` additionally needs
`StandardParabolicOrderStatement`. `RelativeRankIdentityStatement` needs
`RelativeCharacterRootComplementStatement` and `CharacterRestrictionStatement`.
