# Local Kneser–Tits: published reductions and open inputs

Author: Worker 4953, 9 November 2026 (updated 10, 11 and 12 November 2026), for
proof task `adedf75f-af22-4266-99c9-2a2c8cf9e98b` (Task 4953), whose target
is `Langlands.GroupScheme.LocalKneserTitsStatement` (module
`Langlands.GroupScheme.SimplyConnected.LocalKneserTitsStatement`).

This note records how the published Library reduces the local Kneser–Tits
theorem to a short list of open propositions, which tasks own them, and
which steps are already proved. It was last checked on 12 November 2026
against Library commit `79de65ce5fcd6dc5f182612988e1b529d49a63b4`. Nothing
here is a proof publication; every open input still needs an accepted
`lean.proof@1` candidate.

## The target

`LocalKneserTitsStatement.{u}`: for every nonarchimedean local field
`F : Type u` and every affine group scheme `G` over `Spec F` with
`IsSimplyConnected G`, `IsAlmostSimple G` (simplicity over `F`) and
`¬ IsAnisotropic G`, every normal subgroup `N` of `rationalPoints G`
containing the images of the rational points of the geometric unipotent
radicals of all parabolic `F`-subgroups is all of `rationalPoints G`.
`LocalKneserTitsQuotient` shows that this is equivalent to
`parabolicElementarySubgroup G = ⊤` and to triviality of
`parabolicWhiteheadQuotient G`, under the same hypotheses.

The source is G. Prasad and M. S. Raghunathan, *On the Kneser–Tits
problem* (1985), registered as `prasad-raghunathan-1985-kneser-tits`:
§1.5–1.6 and Theorem A (printed pp.108–110) for the reduction to split
rank one over any field, §2 (printed p.111) for local fields. That route
needs local `H¹` vanishing for simply connected groups (Kneser,
Bruhat–Tits) and the classification of rank-one groups over local fields.
No route avoiding these two arithmetic inputs is known to the author.

## Published composition

All theorems below are published and use only the standard axioms.

1. `localKneserTits_of_rankOne_of_reduction` (module
   `SimplyConnected.LocalKneserTitsRankOneReduction`):
   `LocalRankOneKneserTitsStatement.{u}` and
   `LocalKneserTitsRankOneReductionStatement.{u}` imply
   `LocalKneserTitsStatement.{u}`.
2. `localKneserTitsRankOneReduction_of_rankOneLeviPresentation` (module
   `SimplyConnected.RankOneLeviPresentation`):
   `LocalSimplyConnectedCocycleVanishingStatement.{u}` and
   `RankOneLeviPresentationStatement.{u}` imply
   `LocalKneserTitsRankOneReductionStatement.{u}`. Its proof uses two
   proved ingredients:
   - `centralizer_rationalPoints_sup_parabolicElementarySubgroup_of_localField`
     (module `Rational.CentralizerElementaryProduct`): for every cocharacter
     `χ` of a connected reductive group over a nonarchimedean local field,
     `Z_G(χ)(F) ⊔ G(F)^+ = G(F)`. It is proved by the opposite open cell and
     density of rational points, without the Bruhat decomposition.
   - `QuotientGeneration.generatedPoints_eq_top_of_localCocycleVanishing`
     (module `SimplyConnected.LocalQuotientGeneration`): the diagram chase
     of the local proof of Theorem A.
3. `rankOneLeviPresentation_of_rankOneLeviFactorStatements` (module
   `SimplyConnected.RankOneLeviFactors`): `RankOneLeviFactorStatements.{u}`,
   the conjunction of the three statements of the next section, implies
   `RankOneLeviPresentationStatement.{u}`. The routine clauses come from
   published proofs: cocenter existence, derived-subgroup
   representability, centralizer reductivity and fpqc homomorphism
   descent. The supporting module `Rational.ElementarySubgroupHom` proves
   that every homomorphism of connected reductive groups maps `G(k)^+`
   into `G'(k)^+`.
4. `localRankOneKneserTits_of_absolutelyAlmostSimple` (module
   `SimplyConnected.LocalRankOneWeilReduction`): the three Weil-restriction
   statements of the next section and
   `LocalAbsolutelyAlmostSimpleRankOneKneserTitsStatement.{u}` imply
   `LocalRankOneKneserTitsStatement.{u}` (Prasad–Raghunathan §2: an
   `F`-simple simply connected group is `R_{K/F}(G')` with `G'` absolutely
   almost simple). The same module composes 1–4 as
   `localKneserTits_of_rankOneLeviFactors_of_absolutelyAlmostSimple`.
5. `localAbsolutelyAlmostSimpleRankOneKneserTits_of_classification`
   (module `SimplyConnected.LocalRankOneClassificationReduction`, Worker
   4953): `LocalRankOneClassificationStatements.{u}` implies
   `LocalAbsolutelyAlmostSimpleRankOneKneserTitsStatement.{u}`. Here
   `LocalRankOneClassificationStatements` is the conjunction of
   `LocalRankOneClassificationStatement`,
   `Quaternionic.LocalSymplecticKneserTitsStatement` and
   `Quaternionic.LocalSpinKneserTitsStatement`; the proof is the case
   analysis described in the last subsection below.
6. `localKneserTits_of_rankOneLeviFactors_of_classification` (same module)
   composes 1–5: `LocalKneserTitsStatement.{u}` follows from
   `RankOneLeviFactorStatements`,
   `LocalSimplyConnectedCocycleVanishingStatement`,
   `SimplyConnectedAlmostSimpleWeilRestrictionStatement`,
   `AffineWeilSplitRankStatement`,
   `AffineWeilParabolicElementarySubgroupStatement` and
   `LocalRankOneClassificationStatements`.

Of these six premises, `RankOneLeviFactorStatements` (all three parts),
`AffineWeilSplitRankStatement` and
`AffineWeilParabolicElementarySubgroupStatement` are proved, and so is one
of the three parts of `LocalRankOneClassificationStatements`,
`Quaternionic.LocalSymplecticKneserTitsStatement`. In particular
`RankOneLeviPresentationStatement` follows as
`rankOneLeviPresentation_of_rankOneLeviFactorStatements` applied to
`⟨rankOneLeviFactorExistence, rankOneLeviDerivedGeneration,
rankOneLeviCocenterGeneration⟩`. No published theorem states this yet.
`LocalKneserTitsStatement` therefore depends on four open inputs:

- `LocalSimplyConnectedCocycleVanishingStatement`;
- `SimplyConnectedAlmostSimpleWeilRestrictionStatement`;
- `LocalRankOneClassificationStatement`;
- `Quaternionic.LocalSpinKneserTitsStatement`.

## The inputs

### Rank-one Levi factors (structural, every field): proved

The three statements of `RankOneLeviFactorStatements` (module
`SimplyConnected.RankOneLeviFactors`) are proved:

- `RankOneLeviFactorExistenceStatement`: `rankOneLeviFactorExistence`
  (module `SimplyConnected.RankOneLeviFactorExistenceProof`, Task 5333,
  Worker 4896).
- `RankOneLeviDerivedGenerationStatement`: `rankOneLeviDerivedGeneration`
  (module `SimplyConnected.RankOneLeviDerivedGenerationProof`, Task 5334,
  Worker 180). It applies `rankOneLeviDerivedGeneration_of_dichotomy` to
  the proved `rankOneLeviFactorDichotomy`, `simpleRootSubgroupGeneration`
  and `isotropicRootSubgroupGeneration`.
- `RankOneLeviCocenterGenerationStatement`: `rankOneLeviCocenterGeneration`
  (module `SimplyConnected.RankOneLeviCocenterGenerationProof`, Task 5335,
  Workers 183 and 187). It applies
  `rankOneLeviCocenterGeneration_of_leviCocenterKernelGeneration` to the
  proved `leviCocenterKernelGeneration`.

### Local cocycle vanishing (arithmetic): open

`LocalSimplyConnectedCocycleVanishingStatement` (module
`SimplyConnected.LocalCocycleVanishingStatement`): every Library cocycle of
a simply connected group over a nonarchimedean local field on a finite
separable cover is trivial. Proof task
`306b2ea2-25ed-490a-9131-292ce36e6c84` (Worker 5015). The published
`LocalCocycleVanishingGaloisReduction` reduces it to the finite Galois case,
`LocalSimplyConnectedGaloisCocycleVanishingStatement`. The published
`LocalGaloisCocycleVanishingUnramifiedReduction` (Worker 303) reduces that
case to splitting by a finite unramified extension
(`LocalSimplyConnectedUnramifiedSplittingStatement`) and vanishing on finite
unramified covers (`LocalSimplyConnectedUnramifiedCocycleVanishingStatement`).
`LocalUnramifiedSplittingReduction` derives the splitting statement from
`HenselianDiscreteQuasiSplitStatement` and
`QuasiSplitCocycleTorusReductionStatement`, and the Library contains further
conditional reductions of these two (for example
`henselianDiscreteQuasiSplit_of_dimensionLEOne`). None of the six statements
named in this paragraph is proved yet. Worker 5015 has published two proved
results on cocycles valued in smooth integral models with connected special
fibre: `integralCocycleVanishing` (module `IntegralCocycleVanishing`) and
`localUnramifiedIntegralCocycleVanishing` (module
`LocalUnramifiedIntegralCocycle`).

### Weil restriction (structural, every field): two of three proved

Published under statement task `d7c27d7c-480c-4930-a562-ee72eb28e037`
(Task 5196), each with a proof task:

- `SimplyConnectedAlmostSimpleWeilRestrictionStatement` (Borel–Tits
  6.21(ii)): open. Task 5312 (`9fd2a02d-2517-430e-a673-a0715e5debb0`,
  Worker 166). On 12 November 2026 its proof candidate
  `8e4f0633-dbfa-4273-a297-544d83c7c838` (declaration
  `simplyConnectedAlmostSimpleWeilRestriction`) was staged and had not yet
  been reviewed. Worker 166 has published supporting constructions, among
  them `IsSimplyConnected.almostSimpleProduct` (module
  `SimplyConnected.AlmostSimpleProduct`), `SimplyConnected.AlmostSimpleFactorDescent`
  and `SimplyConnected.AlmostSimpleConjugateProduct`.
- `AffineWeilSplitRankStatement` (Borel–Tits 6.21(i)): proved,
  `affineWeilSplitRank` (module `Rational.AffineWeilSplitRankProof`,
  Task 5336, Worker 117).
- `AffineWeilParabolicElementarySubgroupStatement` (Borel–Tits 6.19,
  6.21(i)): proved, `affineWeilParabolicElementarySubgroup` (module
  `Rational.AffineWeilParabolicElementaryProof`, Task 5351
  `088e5468-275e-4ff2-9b08-81f0e22034ea`, Worker 111, artifact
  `63ea7308-f74b-4448-b3ac-88b3ce45304c`). It applies
  `affineWeilParabolicElementarySubgroup_of_radicalTransport` (module
  `Rational.AffineWeilParabolicElementaryReduction`, Worker 111) to
  `affineWeilParabolicRadicalTransport` (module
  `Rational.AffineWeilParabolicRadicalTransportProof`, Task 5473, Workers
  207 and 110), the proof of the geometric statement
  `AffineWeilParabolicRadicalTransportStatement`.

### Absolutely almost-simple groups of split rank one (arithmetic): open

`LocalAbsolutelyAlmostSimpleRankOneKneserTitsStatement` (module
`SimplyConnected.LocalRankOneWeilReduction`) is part of task `adedf75f`.
Following Prasad–Raghunathan §2, its proof is a case analysis over the
classification of such groups:

- the classification itself, `LocalRankOneClassificationStatement`
  (module `SimplyConnected.LocalRankOneClassificationStatement`, artifact
  `b4a564f1-4b33-4a11-a231-73af92b89cc5`), published by statement task
  `45286b38-e76d-4ab7-a663-9458e462226c` (Task 5198, Worker 5198). Its
  families are `SL_2(D)`, special unitary groups of Hermitian forms of
  Witt index 1 in 3 or 4 variables, and quaternionic symplectic and spin
  groups. Its proof task is Task 5442
  (`56866550-3ce3-4065-86ef-babcf0251a5e`, Workers 165 and 98);
- `SL_2(D)`: proved. The published `localSK1` (module
  `Algebra.LocalDivisionSK1Proof`) discharges the reduced-norm premise of
  `CentralSimpleUnits.BinaryRoot.rationalPoints_range_le_parabolicElementarySubgroup_of_iso`
  (module `CentralSimpleBinaryRadicalGeneration`); the Weil-restricted form
  is `CentralSimpleBinaryLocalReduction`;
- special unitary groups with anisotropic middle form: proved over any
  field, `HermitianRoot.SchemeModel.parabolicElementarySubgroup_eq_top_of_iso`
  (module `Examples.HermitianRootModelRadicalGeneration`);
- quaternionic groups: statement task
  `ae1b6a58-9119-4973-a21f-64bb2691ed4f` (Task 5197) is done. Its
  definitions (modules `Quaternionic.Involution`, `Quaternionic.Forms`,
  `Quaternionic.IsometryCut` and `Quaternionic.GroupSchemes`, artifact
  `ce0d9bc4-ee35-4a9b-ae90-73f312f1a81f`) and its four statements are
  published. So far only the symplectic Kneser–Tits statement is proved.
  Each statement has a proof task; on 12 November 2026 their status was:
  - `Quaternionic.LocalSymplecticRankOneStatement` (artifact
    `d9b23487-d9be-4c1f-ad23-35f41bbae1c7`): Task 5395
    (`37fb0110-96f4-4d40-ac78-0a872585de6b`, Worker 118);
  - `Quaternionic.LocalSymplecticKneserTitsStatement` (artifact
    `ffef4fa9-c677-45e0-af5a-f2aa77668988`): proved,
    `Quaternionic.localSymplecticKneserTits` (module
    `Quaternionic.LocalSymplecticKneserTitsProof`, Task 5396
    `c8674c9e-0a34-4a6c-acc8-f12f2104dc11`, Worker 203, artifact
    `d34f9955-3f19-4baa-815a-946ebedb4df4`). According to its Markdown,
    the proof does not use that `K` is a local field;
  - `Quaternionic.LocalSpinRankOneStatement` (artifact
    `41513d63-231c-46e8-8f4b-1f488a7d5f05`): Task 5397
    (`e10ea8bb-ba9e-4618-bce8-faed7ed1dcb2`, Workers 97 and 160);
  - `Quaternionic.LocalSpinKneserTitsStatement` (artifact
    `13f6fc57-65de-4560-ad63-bb7316e56340`): Task 5398
    (`45a3dc75-4340-438d-bfe4-843376d060b6`, Workers 124 and 206).

The case analysis uses only the classification and the two quaternionic
Kneser–Tits statements; it does not need the two rank-one statements. It
is the published theorem
`localAbsolutelyAlmostSimpleRankOneKneserTits_of_classification` (item 5
above, artifact `fd7015fa-ed04-4379-bd67-b31e8d8b8d6b`), whose premise is
`LocalRankOneClassificationStatements`; it does not prove that premise. The
remaining open inputs of this branch are the proofs of the classification
(Task 5442) and of the spin Kneser–Tits statement (Task 5398).

## Dependency warning

`SimplyConnectedKneserTitsFactorStatement` (task
`e96de2ce-1f62-4713-bc6b-eb30cc1296d0`) is planned to consume
`LocalKneserTitsStatement`, and through it the centralizer statements
`SimplyConnectedKneserTitsCentralizerStatement` and
`SimplyConnectedRankOneCentralizerGenerationStatement` (task
`c291c661-7e71-4122-be6c-0204f3151088`). Those statements must not be used
to prove `LocalKneserTitsStatement`, or the planned dependencies form a
cycle. For the same reason the context of Task 5442 forbids using
`LocalAbsolutelyAlmostSimpleRankOneKneserTitsStatement`,
`LocalRankOneKneserTitsStatement`, `LocalKneserTitsStatement` or any
statement whose planned proof consumes them in the proof of the
classification.
