# Group schemes: unproved targets that published reductions already close

This note records a status scan of the Library on 8 November 2026 at commit
`c4a16df784376405a45b60df82583e8c26d8a4e3`; the statuses it reports (open,
composable, directly proved) are those of that commit. The
[last section](#present-status) gives the present status of the targets. Many published proposition targets
under `Langlands.GroupScheme` have no direct proof, but published conditional
reductions and published unconditional proofs together imply them. The note lists
68 such targets found in three rounds of the scan, with the exact composite terms.
It gives a compile-checked proof route from published inputs
to `ParabolicDynamicStatement` (Milne 25.1), which round 2 needs. It also names the
open premises that blocked the most other statements. The note itself proves
nothing; its composite terms were compile-checked as described below.

## Method and evidence

The scan used Lean itself as a scripting tool. In a private file, a `#eval` with
`IO` walked every `.lean` file under `Langlands/` in the Library checkout. It
recorded each `def`/`abbrev` whose name ends in `Statement` (794 under
`Langlands/GroupScheme` and the Deligne modules). It classified each `theorem` by
its conclusion:

- a direct proof has a bare statement as its conclusion and no statement-valued
  hypotheses;
- a conditional theorem has statement-valued hypotheses or an implication
  conclusion;
- a reduction definition is a statement whose body is `A → B → … → C` with every
  factor a statement.

A fixpoint over these records found the statements implied by direct proofs. The
script then generated one term per statement, and that file was compiled
against the Library. Text
parsing over-approximates. Twenty-one generated terms failed or depended on a
failed term and were removed. In those terms an "input proof" was itself
conditional, a namespace was misread, or the target takes parameters. The final
file had no errors. `Lean.collectAxioms` reported only `propext`,
`Classical.choice` and `Quot.sound` for all 53 remaining theorems. Rounds 2 and 3
below were checked the same way.

Practical points for repeating such a scan:

- the Library checkout is readable from `#eval` by absolute path, but the file
  system is read-only, so print results as diagnostics;
- in the pinned Lean, `String.drop` and `String.trimLeft` return `String.Slice`;
  work with `s.toList` and `String.ofList`;
- imported constants are in `env.constants.map₁`, not `map₂`.

## Round 1: 53 composable targets

Names are in `Langlands.GroupScheme` unless written in full. Each row gives the
conditional theorem applied, then its inputs. An input written `(X row)` means the
composite term in the row for target `X`.

### The first nineteen targets

| Target | Composite term |
| --- | --- |
| `RelativeRootSystemStatement` | `relativeRootSystemStatement_of_rootRankOneFactorizationStatement rootRankOneFactorization` |
| `StandardLeviConjugationStatement` | `standardLeviConjugationStatement_of_relativeRootSystemStatement (RelativeRootSystem row)` |
| `StandardCocharacterStatement` | `standardCocharacterStatement_of_relativeRootSystem_of_signs (RelativeRootSystem row) relativeRootSignsDetermineDynamic` |
| `RelativeSimpleRootBasisStatement` | `relativeSimpleRootBasisStatement_of_relativeRootSystemStatement (RelativeRootSystem row)` |
| `RenardRootConventionStatement` | `renardRootConventionStatement_of_relativeRootSystem (RelativeRootSystem row)` |
| `StandardLeviIntersectionStatement` | `Langlands.Jacquet.standardLeviIntersection_of_relativeRootSystem (RelativeRootSystem row)` |
| `StandardRootAnnihilatorRankStatement` | `standardRootAnnihilatorRank_of_standardCocharacter (StandardCocharacter row)` |
| `StandardLeviSplitComponentStatement` | `standardLeviSplitComponent_of_structural_statements (StandardCocharacter row) splitComponentStatement leviSplitComponentStatement` |
| `RelativeRoot.RelativeRootRayDecompositionStatement` | `RelativeRoot.relativeRootRayDecompositionStatement_of_rootRankOneFactorizationStatement rootRankOneFactorization` |
| `RelativeRoot.RootSubgroupVectorStatement` | `RelativeRoot.rootSubgroupVectorReduction (RelativeRootSystem row) RelativeRoot.semigroupRealization RelativeRoot.semigroupCommutator RelativeRoot.cyclicRootFunctorComparison RelativeRoot.cyclicWeightFiltration` |
| `SplitParabolicCocharacterStatement` | `splitParabolicCocharacterStatement_of_absoluteBorelOvergroup borelConjugacy absoluteBorelOvergroupCocharacter maximalTorusBaseChange` |
| `DerivedSubgroupSemisimpleStatement` | `derivedSubgroupSemisimple_of_rootDatum_product rootDatumExistence derivedMaximalTorusProductSurjectivity` |
| `ReductiveCentralDerivedProductStatement` | `reductiveCentralDerivedProduct_of_surjectivity derivedSubgroupRepresentability reductiveCentralTorusSurjectivity` |
| `NormalUnipotentRadicalIntersectionStatement` | `normalUnipotentRadicalIntersection_of_fixedCenterContainingTorus fixedCenterContainingTorus` |
| `SemisimpleAlmostSimpleGenerationStatement` | `semisimpleAlmostSimpleGeneration_of_rootLines normalReductiveCenter (SemisimpleRootGeneration row) absoluteRootVectorLine maximalTorusConjugacy` |
| `SemisimpleNormalIsogenyComplementStatement` | `semisimpleNormalIsogenyComplement_of_generation (SemisimpleAlmostSimpleGeneration row)` |
| `SemisimpleNormalComplementStatement` | `semisimpleNormalComplement_of_almostSimpleGeneration (SemisimpleAlmostSimpleGeneration row)` |
| `NormalAdjointEquivariantRetractionStatement` | `normalAdjointEquivariantRetraction_of_semisimpleNormalComplement (SemisimpleNormalComplement row)` |
| `SimplyConnectedAlmostSimpleRationalGenerationStatement` | `simplyConnectedAlmostSimpleRationalGeneration_of_normalIsogenyComplement (SemisimpleNormalIsogenyComplement row)` |

### The remaining thirty-four targets

The 34 remaining targets fall into three groups.

- Sixteen reductive-structure targets over fields: `AlgClosedMaximalTorusCentralizerStatement`,
  `CenterMultiplicativeTypeStatement`, `SemisimpleRootGenerationStatement`,
  `SemisimpleNormalRootDichotomyStatement`, `RootDatumUniquenessStatement`,
  `SplitPinningExistenceStatement`, `RankOneAlgClosedPositiveRootUniquenessStatement`,
  `RankOneAlgClosedBorelExclusionStatement`,
  `AlgebraicallyClosedSemisimplePerfectStatement`,
  `ReductiveTorusPowerDominationStatement`,
  `ReductiveGeometricSolvableRadicalExistsStatement`,
  `DynamicUnipotentUnipotenceStatement`,
  `Lie.ConnectedReductiveAdjointDeterminantStatement`,
  `SuppliedCocenterTorusStatement`,
  `CharacteristicZeroReductiveInvariantIntegralStatement` and
  `FlagCoreDualLineStatement`.
- Nine torus and maximal-torus targets: `NoTorusBaseChangeStatement`,
  `CentralMaximalTorusBaseChangeStatement`, `MaximalTorusBaseChangeForwardStatement`,
  `SemisimpleCentralizerConjugationDataStatement`,
  `SemisimpleCentralizerConjugatorReductionStatement`,
  `MaximalTorusConjugatorReductionStatement`, `MaximalTorusGenericConjugatorStatement`,
  `TorusGeneratedEnvelopeAlgebraicClosureInfiniteStatement` and
  `TorusSubgroupModuli.ChartCoverStatement`.
- Nine rational-structure, quotient and local-splitting targets: `SplitTorusCentralizerReductiveStatement`,
  `RelativeRoot.ActualRootCyclicComparisonStatement`,
  `NoProperPseudoParabolicSplitTorusCentralStatement`,
  `AnisotropicPointsCompactnessStatement`, `AlgClosedNormalQuotientExistenceStatement`,
  `AffineNormalSubgroupQuotientStatement`, `InvariantPointedImageGenerationStatement`,
  `LocalSplitRootGroupStatement` and `LocalSplitCell.LocalWeylNormalizationStatement`.

Two examples show the pattern. `DynamicUnipotentUnipotenceStatement` (CGP Lemma
2.1.5 over a field) is `dynamicUnipotentUnipotenceReduction unitriangularUnipotent
unipotentClosedSubgroup`. `CenterMultiplicativeTypeStatement` is
`centerMultiplicativeTypeCentralizerReduction` applied to the composite for
`AlgClosedMaximalTorusCentralizerStatement`, which is
`algClosedMaximalTorusCentralizerReduction dynamicCentralizerReductive
noTorusUnipotent solvableTorusQuotient`.

## Round 2: `ParabolicDynamicStatement` and its consequences

`ParabolicDynamicStatement` (module `Absolute.BorelStatement`) is Milne's Theorem
25.1 in the Library's formulation. Over every field `k`, a closed subgroup
`i : P ⟶ G` of a connected reductive `G` is parabolic exactly when its range is
`Dynamic.parabolic χ` for a cocharacter `χ` defined over `k`. The Library proves
it, as `parabolicDynamic` (`Absolute/ParabolicDynamicProof.lean`). The text scan
found no reduction concluding it. Nevertheless every input is published, apart from
`SplitParabolicCocharacterStatement`, which round 1 composes. The following proof
compiled, with the same axiom report:

- **(⇐)** This direction is the published
  `isParabolicSubgroup_of_range_eq_dynamicParabolic` (module
  `Absolute.DynamicParabolicRecognition`).
- **(⇒)** This direction has four steps:
  1. `parabolicMaximalTorus` (module `Absolute.ParabolicMaximalTorusProof`) gives a
     maximal torus `j : T ⟶ G` over `k` with `f ≫ i = j`.
  2. `torusFiniteGaloisSplitting` gives a finite Galois `K/k` splitting `T`.
  3. Over `K` it applies `IsConnectedReductive.baseChange_of_algebraicExtension`,
     `maximalTorusBaseChange` and `parabolicFieldExtensionStatement` (module
     `Absolute.ParabolicFieldExtensionProof`). The round-1 `SplitParabolicCocharacter`
     composite then gives `ν` with `range(i_K) = P(ν ≫ j_K)`.
  4. `exists_range_eq_parabolic_iff_finiteGaloisBaseChange` (module
     `Absolute.FixedTorusGaloisDescent`) descends `ν`, by an integral Galois orbit sum,
     to a cocharacter `μ` of `T` over `k` with `range(i) = P(μ ≫ j)`.

```lean
theorem parabolicDynamic : ParabolicDynamicStatement.{u} := by
  intro k _ G hG P i hi
  constructor
  · intro hP
    have : Smooth G.X.hom := hG.smooth
    have : IsAffineHom G.X.hom := hG.isAffineHom
    have : ConnectedSpace G.X.left := hG.connectedSpace
    have : IsClosedImmersion i.hom.hom.left := hi
    have : Mono i.hom.hom := Over.mono_of_mono_left _
    obtain ⟨T, j, f, hj, hfj⟩ := parabolicMaximalTorus k G hG P i hP
    have : IsClosedImmersion j.hom.hom.left := hj.2.1
    have : IsAffineHom T.X.hom := by
      rw [← Over.w j.hom.hom]
      infer_instance
    obtain ⟨K, _, _, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting k T.toGrp hj.1
    have : FiniteDimensional k K := hfin
    have : IsGalois k K := hgal
    have : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
    have hTK : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp :=
      hsplit
    obtain ⟨mu, hmu⟩ :=
      (exists_range_eq_parabolic_iff_finiteGaloisBaseChange k K T j i hTK).mpr (by
        have hGK : IsConnectedReductive
            ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
          hG.baseChange_of_algebraicExtension
        have hjK : IsMaximalTorus
            (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
            ((GroupScheme.baseChange (algebraBaseMap k K)).map j) :=
          (maximalTorusBaseChange k K G T j hj.1 hj.2.1).1 hj
        have hPK := parabolicFieldExtensionStatement k K G hG P i hP
        have hfK : (GroupScheme.baseChange (algebraBaseMap k K)).map f ≫
            (GroupScheme.baseChange (algebraBaseMap k K)).map i =
              (GroupScheme.baseChange (algebraBaseMap k K)).map j := by
          rw [← Functor.map_comp, hfj]
        exact splitParabolicCocharacterStatement_of_absoluteBorelOvergroup borelConjugacy
          absoluteBorelOvergroupCocharacter maximalTorusBaseChange K _ hGK _ _ hTK hjK _ _ _
          hPK hfK)
    exact ⟨CommGroupScheme.groupHom mu ≫ j, hmu⟩
  · rintro ⟨χ, hχ⟩
    exact isParabolicSubgroup_of_range_eq_dynamicParabolic hG i hi χ hχ
```

The proof sits in namespace `Langlands.GroupScheme` under `noncomputable section`,
with `open CategoryTheory AlgebraicGeometry`. It imports the `Langlands.GroupScheme`
modules `Absolute.BorelStatement`, `Absolute.DynamicParabolicRecognition`,
`Absolute.ParabolicMaximalTorusProof`, `Absolute.ParabolicFieldExtensionProof`,
`Absolute.FixedTorusGaloisDescent`, `Absolute.SplitParabolicCocharacterAbsoluteReduction`,
`Absolute.BorelConjugacyProof`, `Absolute.BorelOvergroupCocharacterProof`,
`Torus.MaximalBaseChangeProof`, `Torus.FiniteGaloisSplittingProof` and
`Reductive.AlgebraicExtensionAscent`. The cocharacter is defined over `k`. No
root-system, conjugacy or Levi-existence premise is added.

Given a proof `PD` of `ParabolicDynamicStatement`, published reductions close eight
more targets. Each composite compiled with the same axiom report.

| Target | Composite term |
| --- | --- |
| `ParabolicSelfNormalizerStatement` | `parabolicSelfNormalizerStatement_of_rational_descent borelConjugacy borelNormalizer PD dynamicConnected` |
| `DynamicSemistandardIntersectionStatement` | `dynamicSemistandardIntersection_of_structural PD dynamicCentralizerReductive dynamicGeometricUnipotentRadical` |
| `FiniteFieldCentralCocharacterSolvableStatement` | `finiteFieldCentralCocharacterSolvable_of PD finiteFieldQuasiSplit` |
| `ParabolicRadicalTorusCentralizerLeviStatement` | `parabolicRadicalTorusCentralizerLevi_of_dynamic PD dynamicCentralizerReductive solvableMaximalTorusConjugacy` |
| `ParabolicGeometricSolvableRadicalExistsStatement` | `parabolicGeometricSolvableRadicalExists_of_structure PD dynamicCentralizerReductive (ReductiveGeometricSolvableRadicalExists composite of round 1)` |
| `ParabolicRadicalTorusLeviStatement` | `parabolicRadicalTorusLevi_of_structural_inputs (previous row) maximalRankRadicalTorusIntersection maximalTorusBaseChange borelContainingSubgroupConnectedStatement (ParabolicRadicalTorusCentralizerLevi row) maximalTorusCentralizer` |
| `RepresentedParabolicLeviIntersectionStatement` | `representedParabolicLeviIntersection_of_dynamic PD dynamicCentralizerReductive` |
| `ParabolicRadicalTorusInitialCentralizerLeviStatement` | `parabolicRadicalTorusInitialLevi_of_dynamic PD dynamicCentralizerReductive` |

Two more published reductions take `PD` but need a further hypothesis:
`DynamicLeviConjugacy.rationalLeviConjugacy_of_dynamic` needs a unipotent conjugation
property of dynamic cocharacters, and
`RelativeParabolicQuotient.existenceStatement_of_statements` needs
`RelativeParabolicQuotient.ProperAmbientCriterion`.

## Round 3: the two root-system premises

`RootGeneratedCentralizerStructuralPremises` (module
`Rational.RootGeneratedCentralizerReduction`) is the conjunction
`RelativeRootSystemStatement ∧ RootRankOneFactorizationStatement`. The text scan first
missed it, because the conjunction's name does not end in `Statement`. Both conjuncts are now available:
`⟨(RelativeRootSystem composite), rootRankOneFactorization⟩`. These seven targets then compiled, with the same axiom report:

| Target | Composite term (`H` = the conjunction above) |
| --- | --- |
| `RelativeRootReflectionExistenceStatement` | `relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization` |
| `RelativeWeylCoxeterStatement` | `H.relativeWeylCoxeter` |
| `StandardRelativeWeylGenerationStatement` | `standardRelativeWeylGenerationStatement_of_relativeWeylCoxeter (previous row)` |
| `RootGeneratedCentralizerRankOneStatement` | `rootGeneratedCentralizerRankOne_of_structuralPremises H` |
| `RelativeRoot.DynamicRootOrderedProductStatement` | `H.dynamicRootOrderedProduct` |
| `ParabolicRootPresentationIndependenceStatement` | `parabolicRootPresentationIndependenceStatement_of_reflections (first row)` |
| `ParabolicRootPresentationIsoStatement` | `parabolicRootPresentationIsoStatement_of_reflections (first row)` |

`RationalBruhatStatement`, and through it `RelativeTitsSystemStatement`, still needs
`RationalBruhatStructuralInputs`. That structure bundles `GenericMinimalParabolicStatement`,
`ParabolicIntersectionCentralizerStatement` and
`MinimalParabolicSplitTorusConjugacyStatement`, which were open at the scanned
commit, with two proved inputs.

## Near misses that are not closed

These conditional theorems appeared composable from the text scan, but one of their
inputs is itself conditional. These terms do not close the targets:

- `SimplyConnectedPositiveCharConjugationMapStatement`,
  `SteinbergCovariantExhaustionStatement` and `SteinbergTensorEmbeddingStatement`:
  `steinbergBigCell_of_inputs` needs `SteinbergBigCellInputs`.
- `RelativeIdentityComponent.SmoothNormalityStatement` and `SmoothBaseChangeStatement`:
  `smoothExistence_of_isOpen` needs openness of the identity component.
- `PseudoParabolicQuotientRationalLiftingStatement` and its consumers
  `SplitTorusIntoPseudoParabolicStatement`, `SplitSolvableIntoPseudoParabolicStatement`,
  `SmoothMaximalSplitTorusDescentStatement` and `SmoothMaximalSplitTorusConjugacyStatement`:
  the split-radical induction step still has a structural premise.
- `ParabolicIntersectionGeometryStatement` and `ParabolicIntersectionTorusStatement`:
  `parabolicIntersectionGeometry_of_commonTorus` also needs a common-torus hypothesis.
- `ClassFunctions.AlgClosedStronglyRegularFibresStatement` and
  `ClassFunctions.StronglyRegularFibresStatement`: a further unipotent-conjugation
  hypothesis remains.

The other four removed terms concern the parametrized propositions
`WeilGm.embeddingSumZeroFixedStatement`, `WeilGm.embeddingQuotientFixedStatement`,
`WeilGm.normOneCocharacterFixedStatement` and `WeilGm.normOneCharacterFixedStatement`.
These take field arguments, so a bare composite term is ill-typed. The text scan
cannot tell whether their published theorems already cover every parameter value;
they need a separate check against the
[norm-one ledger](norm-one-rational-progress.md).

## Open premises that block many statements

`SmoothMaximalSplitTorusConjugacyStatement` and `GenericMinimalParabolicStatement`
have published-input routes, together with sixteen further targets, recorded in
[the smooth split-torus conjugacy note](smooth-split-torus-conjugacy-route.md). The list
below is the state at the scanned commit, before those routes.

The textual classification is approximate. Of the 794 statements, it counted 558
as directly proved, 74 as composable from the text (53 of these survived the
compile check) and 162 as open. The fourteen near misses above were open. Rounds 2
and 3 compile-checked fifteen further targets and the route to
`ParabolicDynamicStatement`. A few "open" statements are only components of proved
conjunctions. For example, the five `GeneralLinear` dynamic statements are proved
through `dynamicStatement`, and the `GL_n` `IsReductiveStatement` through
`reductiveStatement`. Conversely, the scan had counted four of the round-3 targets
as directly proved: `RelativeWeylCoxeterStatement`,
`RootGeneratedCentralizerRankOneStatement`, `DynamicRootOrderedProductStatement` and
`RelativeRootReflectionExistenceStatement`. A theorem with a hypothesis that is not
a statement can be miscounted as a direct proof in this way, so the
"directly proved" count is only an upper bound until checked against declaration
types.

After the three rounds, the open premises that recur most in published conditional
theorems are:

- `SmoothMaximalSplitTorusConjugacyStatement` (Borel–Tits conjugacy of maximal split
  tori). It blocks
  `MinimalParabolicSplitTorusConjugacyStatement`, `ParabolicSplitTorusLeviConjugacyStatement`
  and `DynamicLeviParabolicCorrespondenceStatement`, and through
  `RationalBruhatStructuralInputs` the rational Bruhat and relative Tits statements.
- `GenericMinimalParabolicStatement` and
  `ParabolicIntersectionCentralizerStatement`, the other open Bruhat inputs.
- `SplitSimplyConnectedCorootSpanStatement` (simply connected covers and their
  field-extension behaviour).
- `AdjointQuotientExistenceStatement` (quasi-split inner forms).
- `CharacterRestrictionStatement` (relative central directions and ranks).

## Present status

Every target named in this note, and every open premise of the last section,
is now proved in the Library by a theorem whose type is exactly the statement
(for example `parabolicDynamic` in `Absolute/ParabolicDynamicProof.lean`,
`rationalBruhat` in `Rational/RationalBruhatProof.lean`,
`smoothMaximalSplitTorusConjugacy` in
`Rational/SmoothMaximalSplitTorusConjugacyProof.lean`), with these exceptions:

- `StandardRootAnnihilatorRankStatement`: the Library has the conditionals
  `standardRootAnnihilatorRank_of_standardCocharacter`
  (`Rational/StandardLeviCentralDirectionsAssembly.lean`) and
  `standardRootAnnihilatorRankStatement_of_relativeRootSystemStatement`
  (`Rational/StandardRootAnnihilatorRank.lean`), whose inputs are proved
  (`standardCocharacter`, `relativeRootSystem`); no theorem of the
  statement itself was found.
- `ClassFunctions.AlgClosedStronglyRegularFibresStatement`: only the
  conditional `algClosedStronglyRegularFibres_of`
  (`Rational/ClassFunctionsAlgClosedStronglyRegularFibres.lean`) was found.
- The four parametrized `WeilGm` propositions above: their theorems in
  `Torus/WeilRestrictionNormOneFixedProof.lean` take statement-valued
  hypotheses.
