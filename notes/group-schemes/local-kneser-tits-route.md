# Local Kneser–Tits: published reductions and open inputs

This note, dated 9 November 2026 and updated on 10, 11 and 12 November 2026, concerns
`Langlands.GroupScheme.LocalKneserTitsStatement` (module
`Langlands.GroupScheme.SimplyConnected.LocalKneserTitsStatement`).

This note records how the published Library reduces the local Kneser–Tits
theorem to a short list of propositions, and which steps are proved. It
was checked on 12 November 2026 against Library commit `9951a27f5fd8ebbdc4bbe68eb6be65b1d0c2eb4a`,
when three of these propositions were open; their present status is given
where they are named.

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
This note knows no route avoiding these two arithmetic inputs.

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
   (module `SimplyConnected.LocalRankOneClassificationReduction`): `LocalRankOneClassificationStatements.{u}` implies
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
`SimplyConnectedAlmostSimpleWeilRestrictionStatement`,
`AffineWeilSplitRankStatement` and
`AffineWeilParabolicElementarySubgroupStatement` are proved, and so is
`Quaternionic.LocalSymplecticKneserTitsStatement`, one of the three parts of
`LocalRankOneClassificationStatements`. In particular
`RankOneLeviPresentationStatement` follows as
`rankOneLeviPresentation_of_rankOneLeviFactorStatements` applied to
`⟨rankOneLeviFactorExistence, rankOneLeviDerivedGeneration,
rankOneLeviCocenterGeneration⟩`; this note records no theorem stating this.
At commit `9951a27f`, `LocalKneserTitsStatement` depended on three open inputs,
all three now proved in the Library:

- `LocalSimplyConnectedCocycleVanishingStatement`: `localSimplyConnectedCocycleVanishing`
  (`SimplyConnected/LocalCocycleVanishingProof.lean`);
- `LocalRankOneClassificationStatement`: `localRankOneClassification`
  (`SimplyConnected/LocalRankOneClassificationProof.lean`);
- `Quaternionic.LocalSpinKneserTitsStatement`: `Quaternionic.localSpinKneserTits`
  (`Quaternionic/LocalSpinKneserTitsProof.lean`).

The Library has no theorem of `LocalKneserTitsStatement` under its own name;
it follows by item 6 from the proofs named in this note.

## The inputs

### Rank-one Levi factors (structural, every field): proved

The three statements of `RankOneLeviFactorStatements` (module
`SimplyConnected.RankOneLeviFactors`) are proved:

- `RankOneLeviFactorExistenceStatement`: `rankOneLeviFactorExistence`
  (module `SimplyConnected.RankOneLeviFactorExistenceProof`).
- `RankOneLeviDerivedGenerationStatement`: `rankOneLeviDerivedGeneration`
  (module `SimplyConnected.RankOneLeviDerivedGenerationProof`). It applies `rankOneLeviDerivedGeneration_of_dichotomy` to
  the proved `rankOneLeviFactorDichotomy`, `simpleRootSubgroupGeneration`
  and `isotropicRootSubgroupGeneration`.
- `RankOneLeviCocenterGenerationStatement`: `rankOneLeviCocenterGeneration`
  (module `SimplyConnected.RankOneLeviCocenterGenerationProof`). It applies
  `rankOneLeviCocenterGeneration_of_leviCocenterKernelGeneration` to the
  proved `leviCocenterKernelGeneration`.

### Local cocycle vanishing (arithmetic): proved

`LocalSimplyConnectedCocycleVanishingStatement` (module
`SimplyConnected.LocalCocycleVanishingStatement`): every Library cocycle of
a simply connected group over a nonarchimedean local field on a finite
separable cover is trivial. The Library proves it, as
`localSimplyConnectedCocycleVanishing` (module
`SimplyConnected.LocalCocycleVanishingProof`). The published
`LocalCocycleVanishingGaloisReduction` reduces it to the finite Galois case,
`LocalSimplyConnectedGaloisCocycleVanishingStatement`. The published
`LocalGaloisCocycleVanishingUnramifiedReduction` reduces that
case to splitting by a finite unramified extension
(`LocalSimplyConnectedUnramifiedSplittingStatement`) and vanishing on finite
unramified covers (`LocalSimplyConnectedUnramifiedCocycleVanishingStatement`).
`LocalUnramifiedSplittingReduction` derives the splitting statement from
`HenselianDiscreteQuasiSplitStatement` and
`QuasiSplitCocycleTorusReductionStatement`, and the Library contains further
conditional reductions of these two (for example
`henselianDiscreteQuasiSplit_of_dimensionLEOne`). Of the six statements named
in this paragraph, the Library proves the first, as well as
`LocalSimplyConnectedUnramifiedSplittingStatement`,
`HenselianDiscreteQuasiSplitStatement` and
`QuasiSplitCocycleTorusReductionStatement`; this note records no proof of
the Galois and unramified cocycle-vanishing statements under their own
names. The Library has two proved results on cocycles valued in smooth integral models with connected special
fibre: `integralCocycleVanishing` (module `IntegralCocycleVanishing`) and
`localUnramifiedIntegralCocycleVanishing` (module
`LocalUnramifiedIntegralCocycle`).

### Weil restriction (structural, every field): proved

The three Weil-restriction statements:

- `SimplyConnectedAlmostSimpleWeilRestrictionStatement` (Borel–Tits
  6.21(ii)): proved, `simplyConnectedAlmostSimpleWeilRestriction` (module
  `SimplyConnected.AlmostSimpleWeilRestrictionProof`). Its supporting constructions
  include `IsSimplyConnected.almostSimpleProduct` (module
  `SimplyConnected.AlmostSimpleProduct`), `SimplyConnected.AlmostSimpleFactorDescent`
  and `SimplyConnected.AlmostSimpleConjugateProduct`.
- `AffineWeilSplitRankStatement` (Borel–Tits 6.21(i)): proved,
  `affineWeilSplitRank` (module `Rational.AffineWeilSplitRankProof`).
- `AffineWeilParabolicElementarySubgroupStatement` (Borel–Tits 6.19,
  6.21(i)): proved, `affineWeilParabolicElementarySubgroup` (module
  `Rational.AffineWeilParabolicElementaryProof`). It applies
  `affineWeilParabolicElementarySubgroup_of_radicalTransport` (module
  `Rational.AffineWeilParabolicElementaryReduction`) to
  `affineWeilParabolicRadicalTransport` (module
  `Rational.AffineWeilParabolicRadicalTransportProof`), the proof of the geometric statement
  `AffineWeilParabolicRadicalTransportStatement`.

### Absolutely almost-simple groups of split rank one (arithmetic)

`LocalAbsolutelyAlmostSimpleRankOneKneserTitsStatement` (module
`SimplyConnected.LocalRankOneWeilReduction`).
Following Prasad–Raghunathan §2, its proof is a case analysis over the
classification of such groups:

- the classification itself, `LocalRankOneClassificationStatement`
  (module `SimplyConnected.LocalRankOneClassificationStatement`). Its
  families are `SL_2(D)`, special unitary groups of Hermitian forms of
  Witt index 1 in 3 or 4 variables, and quaternionic symplectic and spin
  groups. The Library proves it, as `localRankOneClassification` (module
  `SimplyConnected.LocalRankOneClassificationProof`). Its prerequisite
  statement `InnerTypeANormOneStatement` (module
  `SimplyConnected.InnerTypeANormOneStatement`) for family (i) is proved,
  as `innerTypeANormOne`;
- `SL_2(D)`: proved. The published `localSK1` (module
  `Algebra.LocalDivisionSK1Proof`) discharges the reduced-norm premise of
  `CentralSimpleUnits.BinaryRoot.rationalPoints_range_le_parabolicElementarySubgroup_of_iso`
  (module `CentralSimpleBinaryRadicalGeneration`); the Weil-restricted form
  is `CentralSimpleBinaryLocalReduction`;
- special unitary groups with anisotropic middle form: proved over any
  field, `HermitianRoot.SchemeModel.parabolicElementarySubgroup_eq_top_of_iso`
  (module `Examples.HermitianRootModelRadicalGeneration`);
- quaternionic groups: the definitions (modules `Quaternionic.Involution`,
  `Quaternionic.Forms`, `Quaternionic.IsometryCut` and
  `Quaternionic.GroupSchemes`) and four statements are in the Library, and
  the Library proves all four:
  - `Quaternionic.LocalSymplecticRankOneStatement`: proved,
    `Quaternionic.localSymplecticRankOne` (module
    `Quaternionic.LocalSymplecticRankOneProof`);
  - `Quaternionic.LocalSymplecticKneserTitsStatement`: proved,
    `Quaternionic.localSymplecticKneserTits` (module
    `Quaternionic.LocalSymplecticKneserTitsProof`). According to its Markdown,
    the proof does not use that `K` is a local field;
  - `Quaternionic.LocalSpinRankOneStatement`: proved,
    `Quaternionic.localSpinRankOne` (module `Quaternionic.LocalSpinRankOneProof`);
  - `Quaternionic.LocalSpinKneserTitsStatement`: proved,
    `Quaternionic.localSpinKneserTits` (module
    `Quaternionic.LocalSpinKneserTitsProof`). The
    Library also reduces it in two published steps:
    `localSpinKneserTits_of_spinInputs` (module
    `Quaternionic.LocalSpinKneserTitsReduction`) derives it from
    `SpinLeviReducedNormSquareStatement` and
    `SpinKernelElementaryStatement`, and
    `localSpinKneserTits_of_spinCoverModel` (module
    `Quaternionic.SpinCoverModelTransport`) derives it from the single
    `SpinCoverModelStatement`, which asks for one spin cover satisfying the
    Levi reduced-norm and kernel conditions. This note records no proof of
    these three statements.

The case analysis uses only the classification and the two quaternionic
Kneser–Tits statements; it does not need the two rank-one statements. It
is the published theorem
`localAbsolutelyAlmostSimpleRankOneKneserTits_of_classification` (item 5
above), whose premise is `LocalRankOneClassificationStatements`; it does not
prove that premise. The inputs of this branch that were open at commit
`9951a27f`, the classification and the spin Kneser–Tits statement, are now
proved (see above).

## Dependency warning

The Library derives `SimplyConnectedKneserTitsFactorStatement` from
`LocalKneserTitsStatement`
(`simplyConnectedKneserTitsFactor_of_localKT_and_structural_inputs`, module
`SimplyConnected.KneserTitsFactorReduction`), and the centralizer statements
`SimplyConnectedKneserTitsCentralizerStatement` and
`SimplyConnectedRankOneCentralizerGenerationStatement` depend on it in turn
(modules `SimplyConnected.KneserTitsCentralizerReduction` and
`SimplyConnected.RankOneCentralizerGenerationReduction`). Those statements
must not be used to prove `LocalKneserTitsStatement`, or the dependencies
form a cycle. For the same reason the proof of the classification must not
use `LocalAbsolutelyAlmostSimpleRankOneKneserTitsStatement`,
`LocalRankOneKneserTitsStatement`, `LocalKneserTitsStatement` or any
statement whose proof uses them.
