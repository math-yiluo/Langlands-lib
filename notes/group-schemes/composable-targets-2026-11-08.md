# Group schemes: unproved targets that published reductions already close

Author: Worker 15, 8 November 2026, for the algebraic and reductive group-scheme
program `2b5e4a00-9d44-49a4-9c89-979fb5b6233e` (Task 3483).

This note records a status scan of the Library at commit
`c4a16df784376405a45b60df82583e8c26d8a4e3`. Many published proposition targets
under `Langlands.GroupScheme` have no direct proof, but published conditional
reductions and published unconditional proofs together imply them. The note lists
68 such targets found in three rounds, with the exact composite terms and the proof
tasks that own them. It gives a compile-checked proof route from published inputs
to `ParabolicDynamicStatement` (Milne 25.1), which round 2 needs. It also names the
open premises that block the most other statements. Nothing here is a proof
publication. Each target still needs an accepted `lean.proof@1` candidate, and the
standing program remains incomplete.

## Method and evidence

The scan used Lean itself as a scripting tool. In a private draft, a `#eval` with
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
script then generated one candidate term per statement, and that file was compiled
with `lean_check` in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. Text
parsing over-approximates. Twenty-one generated terms failed or depended on a
failed term and were removed. In those terms an "input proof" was itself
conditional, a namespace was misread, or the target takes parameters. The final
file had no errors. `Lean.collectAxioms` reported only `propext`,
`Classical.choice` and `Quot.sound` for all 53 remaining theorems. Rounds 2 and 3
below were checked the same way. This is development evidence only; independent
proof review is still required.

Practical points for repeating such a scan with `lean_check`:

- the Library checkout is readable from `#eval` by absolute path, but the file
  system is read-only, so print results as diagnostics;
- in the pinned Lean, `String.drop` and `String.trimLeft` return `String.Slice`;
  work with `s.toList` and `String.ofList`;
- imported constants are in `env.constants.map₁`, not `map₂`.

## Round 1: 53 composable targets

Names are in `Langlands.GroupScheme` unless written in full. Each row gives the
conditional theorem applied, then its inputs. An input written `(X row)` means the
composite term in the row for target `X`.

### Targets that already have proof tasks

| Target | Composite term | Proof task |
| --- | --- | --- |
| `RelativeRootSystemStatement` | `relativeRootSystemStatement_of_rootRankOneFactorizationStatement rootRankOneFactorization` | `51ecd216-d68e-4f71-afeb-6d7ff3683ec9` |
| `StandardLeviConjugationStatement` | `standardLeviConjugationStatement_of_relativeRootSystemStatement (RelativeRootSystem row)` | `2411603b-373b-4dbe-bcde-69047693b293` |
| `StandardCocharacterStatement` | `standardCocharacterStatement_of_relativeRootSystem_of_signs (RelativeRootSystem row) relativeRootSignsDetermineDynamic` | `5dfe09fb-d1fe-4f5e-8311-8abb7ffc18fc` (a candidate is staged) |
| `RelativeSimpleRootBasisStatement` | `relativeSimpleRootBasisStatement_of_relativeRootSystemStatement (RelativeRootSystem row)` | `ea762b6d-cbce-4e6f-a487-e566db71784e` |
| `RenardRootConventionStatement` | `renardRootConventionStatement_of_relativeRootSystem (RelativeRootSystem row)` | `90eeb314-6b62-4150-bf19-095a45c0ff33` |
| `StandardLeviIntersectionStatement` | `Langlands.Jacquet.standardLeviIntersection_of_relativeRootSystem (RelativeRootSystem row)` | `1d7d4767-a668-4ce1-9989-319a625f6de3` |
| `StandardRootAnnihilatorRankStatement` | `standardRootAnnihilatorRank_of_standardCocharacter (StandardCocharacter row)` | one conjunct of `477e1fb3-dadf-497e-a810-5ae5556f1b12`; the other conjunct stays open |
| `StandardLeviSplitComponentStatement` | `standardLeviSplitComponent_of_structural_statements (StandardCocharacter row) splitComponentStatement leviSplitComponentStatement` | `4bd59665-101a-42d3-a3c7-ba034017ea2f` |
| `RelativeRoot.RelativeRootRayDecompositionStatement` | `RelativeRoot.relativeRootRayDecompositionStatement_of_rootRankOneFactorizationStatement rootRankOneFactorization` | `966b385e-6f61-427b-adcc-4d20e5b832f0` |
| `RelativeRoot.RootSubgroupVectorStatement` | `RelativeRoot.rootSubgroupVectorReduction (RelativeRootSystem row) RelativeRoot.semigroupRealization RelativeRoot.semigroupCommutator RelativeRoot.cyclicRootFunctorComparison RelativeRoot.cyclicWeightFiltration` | `6d7d2b99-6e63-409c-abb5-9d5c08c8d2a9` |
| `SplitParabolicCocharacterStatement` | `splitParabolicCocharacterStatement_of_absoluteBorelOvergroup borelConjugacy absoluteBorelOvergroupCocharacter maximalTorusBaseChange` | `747d4756-e12c-4bb4-9e87-45e11299f7c5` |
| `DerivedSubgroupSemisimpleStatement` | `derivedSubgroupSemisimple_of_rootDatum_product rootDatumExistence derivedMaximalTorusProductSurjectivity` | `6676eb4f-43be-4cd9-88cb-0c28a4f5f859` |
| `ReductiveCentralDerivedProductStatement` | `reductiveCentralDerivedProduct_of_surjectivity derivedSubgroupRepresentability reductiveCentralTorusSurjectivity` | `5dc6c43c-2acc-40a0-92ad-454b4232a509` |
| `NormalUnipotentRadicalIntersectionStatement` | `normalUnipotentRadicalIntersection_of_fixedCenterContainingTorus fixedCenterContainingTorus` | `58fd88de-28b2-4500-a08e-99c2459760b1` |
| `SemisimpleAlmostSimpleGenerationStatement` | `semisimpleAlmostSimpleGeneration_of_rootLines normalReductiveCenter (SemisimpleRootGeneration row) absoluteRootVectorLine maximalTorusConjugacy` | `4573c96e-bda5-414f-8956-9899c669e9a3` |
| `SemisimpleNormalIsogenyComplementStatement` | `semisimpleNormalIsogenyComplement_of_generation (SemisimpleAlmostSimpleGeneration row)` | `f4a3d3d3-3262-412a-8e36-6d650597111b` |
| `SemisimpleNormalComplementStatement` | `semisimpleNormalComplement_of_almostSimpleGeneration (SemisimpleAlmostSimpleGeneration row)` | `f00971f2-9f85-46c8-b7da-c3945f778883` |
| `NormalAdjointEquivariantRetractionStatement` | `normalAdjointEquivariantRetraction_of_semisimpleNormalComplement (SemisimpleNormalComplement row)` | `eaa30c22-e25d-490d-8617-07e05a688c85` |
| `SimplyConnectedAlmostSimpleRationalGenerationStatement` | `simplyConnectedAlmostSimpleRationalGeneration_of_normalIsogenyComplement (SemisimpleNormalIsogenyComplement row)` | `e9ede135-a6ba-4c78-8af2-eb8aa57d25fa` |

### Targets placed in three new proof tasks

Before publishing, the author searched TaskHub for each target's exact name and
found no existing task. The 34 remaining targets went into three `lean.proof@1`
tasks. Each task's context gives the exact term and the modules that contain the
inputs.

- Task 5242, `043f2527-205c-4cfc-b9b2-553de1010d9d`, covers sixteen reductive-structure
  targets over fields: `AlgClosedMaximalTorusCentralizerStatement`,
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
- Task 5243, `054c9e79-c59d-4325-a96b-8c82a40df80b`, covers nine torus and
  maximal-torus targets: `NoTorusBaseChangeStatement`,
  `CentralMaximalTorusBaseChangeStatement`, `MaximalTorusBaseChangeForwardStatement`,
  `SemisimpleCentralizerConjugationDataStatement`,
  `SemisimpleCentralizerConjugatorReductionStatement`,
  `MaximalTorusConjugatorReductionStatement`, `MaximalTorusGenericConjugatorStatement`,
  `TorusGeneratedEnvelopeAlgebraicClosureInfiniteStatement` and
  `TorusSubgroupModuli.ChartCoverStatement`.
- Task 5244, `f60c422f-b0bf-4c73-8b7e-b7383cbf03fc`, covers nine rational-structure,
  quotient and local-splitting targets: `SplitTorusCentralizerReductiveStatement`,
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
`Dynamic.parabolic χ` for a cocharacter `χ` defined over `k`. Its proof task is
`42c85926-0d43-4d0d-abef-f3350c4273ae` (Task 3813). The text scan found no reduction
concluding it. Nevertheless every input is published, apart from
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

| Target | Composite term | Proof task |
| --- | --- | --- |
| `ParabolicSelfNormalizerStatement` | `parabolicSelfNormalizerStatement_of_rational_descent borelConjugacy borelNormalizer PD dynamicConnected` | `1b892972-8cea-419f-812c-f846b494b2bf` |
| `DynamicSemistandardIntersectionStatement` | `dynamicSemistandardIntersection_of_structural PD dynamicCentralizerReductive dynamicGeometricUnipotentRadical` | `55f572c9-7370-45f3-ba97-7f8614d7474e` |
| `FiniteFieldCentralCocharacterSolvableStatement` | `finiteFieldCentralCocharacterSolvable_of PD finiteFieldQuasiSplit` | `46467eff-1d25-48a6-80a4-d5b8e7b3b1ab` |
| `ParabolicRadicalTorusCentralizerLeviStatement` | `parabolicRadicalTorusCentralizerLevi_of_dynamic PD dynamicCentralizerReductive solvableMaximalTorusConjugacy` | `a949d6cb-c272-4a8d-95f2-8a1af0e28e0b` |
| `ParabolicGeometricSolvableRadicalExistsStatement` | `parabolicGeometricSolvableRadicalExists_of_structure PD dynamicCentralizerReductive (ReductiveGeometricSolvableRadicalExists composite of round 1)` | `fd8927d1-6e09-4736-beb0-ad58e39e12ce` |
| `ParabolicRadicalTorusLeviStatement` | `parabolicRadicalTorusLevi_of_structural_inputs (previous row) maximalRankRadicalTorusIntersection maximalTorusBaseChange borelContainingSubgroupConnectedStatement (ParabolicRadicalTorusCentralizerLevi row) maximalTorusCentralizer` | `536b3863-aeea-44e7-ba72-5a54b9a1dcd0` |
| `RepresentedParabolicLeviIntersectionStatement` | `representedParabolicLeviIntersection_of_dynamic PD dynamicCentralizerReductive` | none found |
| `ParabolicRadicalTorusInitialCentralizerLeviStatement` | `parabolicRadicalTorusInitialLevi_of_dynamic PD dynamicCentralizerReductive` | none found |

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
`⟨(RelativeRootSystem composite), rootRankOneFactorization⟩`. Worker 23 pointed out
the reflection route. These seven targets then compiled, with the same axiom report:

| Target | Composite term (`H` = the conjunction above) | Proof task |
| --- | --- | --- |
| `RelativeRootReflectionExistenceStatement` | `relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization` | `5c031416-1958-4d34-a128-56a400781a4b` |
| `RelativeWeylCoxeterStatement` | `H.relativeWeylCoxeter` | `06142774-8bda-49c8-bcd0-f508d9f34199` |
| `StandardRelativeWeylGenerationStatement` | `standardRelativeWeylGenerationStatement_of_relativeWeylCoxeter (previous row)` | `26afc233-452a-4625-87fd-3b9c41f1cb8d` |
| `RootGeneratedCentralizerRankOneStatement` | `rootGeneratedCentralizerRankOne_of_structuralPremises H` | `ca872a17-1adb-4afb-a7cd-d3a1b9680c2e` |
| `RelativeRoot.DynamicRootOrderedProductStatement` | `H.dynamicRootOrderedProduct` | `aecc9605-8fa1-494d-b1e8-946a86638211` |
| `ParabolicRootPresentationIndependenceStatement` | `parabolicRootPresentationIndependenceStatement_of_reflections (first row)` | part of `c6c736b5-f1c4-4203-bb23-f7981c4fc3af` |
| `ParabolicRootPresentationIsoStatement` | `parabolicRootPresentationIsoStatement_of_reflections (first row)` | not found as a separate task |

`RationalBruhatStatement`, and through it `RelativeTitsSystemStatement`, still needs
`RationalBruhatStructuralInputs`. That structure bundles `GenericMinimalParabolicStatement`,
`ParabolicIntersectionCentralizerStatement` and
`MinimalParabolicSplitTorusConjugacyStatement`, which remain open, with two proved
inputs.

## Near misses that are not closed

These conditional theorems appeared composable from the text scan, but one of their
inputs is itself conditional. The targets stay open:

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

Update: `SmoothMaximalSplitTorusConjugacyStatement` and `GenericMinimalParabolicStatement`
now have published-input routes, together with sixteen further targets, recorded in
[the smooth split-torus conjugacy note](smooth-split-torus-conjugacy-route.md). The list
below is the state before that update.

The textual classification is approximate. Of the 794 statements, it counted 558
as directly proved, 74 as composable from the text (53 of these survived the
compile check) and 162 as open. The fourteen near misses above stay open. Rounds 2
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
  tori; task `7c6d89b9-d59a-44ce-aac6-95f9fafe7b82`). It blocks
  `MinimalParabolicSplitTorusConjugacyStatement`, `ParabolicSplitTorusLeviConjugacyStatement`
  and `DynamicLeviParabolicCorrespondenceStatement`, and through
  `RationalBruhatStructuralInputs` the rational Bruhat and relative Tits statements.
- `GenericMinimalParabolicStatement` (task `bc8072c0-8a2b-4636-ab3c-7f04a4afb6a5`) and
  `ParabolicIntersectionCentralizerStatement`, the other open Bruhat inputs.
- `SplitSimplyConnectedCorootSpanStatement` (simply connected covers and their
  field-extension behaviour).
- `AdjointQuotientExistenceStatement` (quasi-split inner forms).
- `CharacterRestrictionStatement` (relative central directions and ranks).
