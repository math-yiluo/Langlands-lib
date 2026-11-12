# Henniart's local construction: statement coverage and dependencies

Author: Worker 14, for task `62ea68fa-e1f4-4187-811b-7436743bba6a` revision 1
(Brauer, virtual-lattice, numerical and finite-witness theorem statements for
Henniart). Most finite-group, lattice and finiteness units below were authored
in the previous instance by Worker 30 for the same task; the finite separating
tests are Worker 78's (task `3862e611-a782-4534-9f5e-6e9a1001ce83`); the
relative global construction is the H3 program (task
`34b81620-20d7-4059-9b08-6bedd1c1c029`, Workers 84 and 116). Each pair names
its own authors.

This note maps the objective of that task to Lean declarations of Library
commit `5263a53b575d66cc4ebc5364c0d990d1b111c7f7`, environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), including the last two units of
this task (`HenniartStableMapStatement` and `HenniartNumericalStatement`,
sections 1.8–1.9). Modules are given relative to `Langlands/`. Consume them by
Lean name from the current Library; the hashes in section 2 fix the versions
described here.

**How to read the status.** Every target below is a `Prop`-valued `def`.
Publication accepts the formulation and its correspondence with the original
source; it does not prove the proposition. "Proved" means the current Library
has a theorem whose type is exactly the named statement, for all values of its
parameters and with no further hypotheses;
"conditional" means a theorem proves it from another named statement;
"closes by composition" means the hypothesis of that conditional theorem is
itself proved, so applying one theorem to the other proves the target, although
no published theorem states the result. All other targets are unproved
obligations; none is an axiom or a structure field. Each
pair's own Markdown gives the exact quantifiers, normalizations, page locators,
registered fingerprints and source gaps; this note summarizes them and does not
replace them.

## 1. Coverage by clause of the objective

### 1.1 Finite character theory and Brauer induction

| Module | Declarations | Original source | Status |
| --- | --- | --- | --- |
| `Representation/Finite/CharacterStatement` | `Langlands.{FiniteCharacterNormalizationStatement, FiniteCompleteReducibilityStatement, FiniteCharacterHomDimensionStatement, FiniteCharacterOrthogonalityStatement, FiniteCharacterIsomorphismStatement, FiniteCharacterNormOneStatement, FiniteCharacterTheoryStatement}` | Serre, *Linear Representations of Finite Groups* (1977), §§1.1, 1.3–1.4, 2.1–2.3 | Proved: `Langlands.FiniteCharacter.finiteCharacterTheory` (`Representation/Finite/CharacterTheoryProof`) |
| `Representation/Finite/BrauerStatement` | `Langlands.FiniteRep.{FiniteRankOneOrderStatement, FiniteInducedCharacterFormulaStatement, FiniteInducedDegreeStatement, FiniteVirtualCharacterFaithfulnessStatement, FiniteIrreducibleBasisStatement, IntegralBrauerSpanningStatement, IntegralBrauerCharacterLatticeStatement, FiniteBrauerTheoryStatement}` | Serre (1977) §§1.2, 7.1–7.2, 9.1, 10.5; Brauer (1947) Thm 1, formula (6), §9; Henniart 2000 §§3.7–3.8 | Proved: `Langlands.FiniteRep.BrauerTheory.finiteBrauerTheory` (`Representation/Finite/BrauerTheoryProof`, with `BrauerLatticeProof`) |
| `Representation/Finite/DegreeZeroBrauerStatement` (Worker 1749) | `Langlands.FiniteRep.FiniteDegreeZeroBrauerStatement` | Deligne (1973) §1.1 and Prop. 1.5, pp.507–510 | Proved: `Langlands.FiniteRep.DegreeZeroBrauer.finiteDegreeZeroBrauer` |
| `VirtualRepresentation/Weil/FiniteQuotientStatement` | `Langlands.VirtualRepresentation.Weil.{FiniteQuotientUnitaryStatement, FiniteQuotientTraceFaithfulnessStatement, FiniteQuotientDegreeStatement, FiniteQuotientPairingStatement, FiniteQuotientPositiveInductionStatement, FiniteQuotientBrauerSpanningStatement, FiniteQuotientSpanBijectionStatement, FiniteQuotientRealizationStatement}` | Henniart 2000 §§2.5–2.6, pp.445–447; Serre (1977) §1.3; Brauer (1947) | Unproved |

In the first three units the coefficient field is `ℂ` and the groups are
finite, the form Henniart uses. The finite-quotient unit applies these results
along a surjective homomorphism `f : G →* H` with open kernel, where `G` is a
topological group that may be infinite and only the quotient `H` is required
finite. It concerns the actual continuous irreducible complex classes of `G`
that factor through `f`. Its degree weights each class by its representation
dimension, and `FiniteQuotientDegreeStatement` identifies that degree with the
trace at the identity. `FiniteQuotientPositiveInductionStatement` says that
each inflated rank-one subgroup induction is an effective element of the
factoring-supported lattice whose degree is the subgroup index.

### 1.2 Weak association, integral descent and the isometry

| Module | Declarations | Original source | Status |
| --- | --- | --- | --- |
| `VirtualRepresentation/DescentStatement` | `Langlands.VirtualRepresentation.{IntegralPairingDefinitenessStatement, IntegralRelationDescentStatement, IntegralGeneratedEquivalenceStatement, IntegralGeneratedIsometryStatement, IntegralGeneratedDegreeStatement, IntegralNormOneSignedBasisStatement, IntegralPositiveDegreeBasisStatement, IntegralIsometryInjectivityStatement, IntegralIsometrySignedBasisStatement, IntegralIsometryPositiveBasisStatement, IntegralDescentAndPositivityStatement}` | Henniart 2000 §§2.5–2.8, pp.445–448 (generic lattice form) | Proved: `Langlands.VirtualRepresentation.integralDescentAndPositivity` (`VirtualRepresentation/DescentProof`) |
| `Global/Factors/RelativePolePairingStatement` (H1/H3) | `Langlands.Global.PoleComparison.{RelativeCertifiedPoleComparisons, RelativeGeneratedPositiveIsometry, RelativePolePairingStatement}` | Henniart 2000 §§2.5–2.8, pp.445–448 | Proved: `Langlands.Global.PoleComparison.relativePolePairing` (`Global/Factors/RelativePolePairingProof`); the statement itself has certified pole comparisons as its hypothesis |
| `Global/Factors/RelativeIsometryOperationStatement` (H3) | `Langlands.Global.PoleComparison.RelativeIsometryOperationStatement` | Henniart 2000 Prop. 2.6 (a), (c) | Unproved; reductions in `Global/Factors/RelativeIsometryOperationReduction` |
| `Global/Factors/RelativeIsometryFactorStatement` (H3) | `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement` | Henniart 2000 Prop. 2.6 (a), (b) | Unproved |

The generic descent unit separates relation descent, generated equivalence,
isometry, degree preservation, injectivity, signed basis correspondence and
positivity as distinct propositions; it does not supply the actual
representation input. The H3 units supply that input at a finite relative level
`E/F` for witnessed pairs (weak automorphic association with their local
factors). Under the certified pole comparisons, `RelativePolePairingStatement`
concludes three things: the local coefficient pairings agree on witnessed
generators; the integral relation kernels of the Weil and automorphic generator
families are equal, which is the weak-association independence on
induced-character relations; and there is a unique linear equivalence `T` from
the generated Weil span to the generated automorphic span satisfying
`RelativeGeneratedPositiveIsometry`. That predicate takes `T` as an argument
and specifies its properties: `T` sends each witnessed Weil generator to its
automorphic partner, preserves pairings and degrees, and sends each
positive-degree norm-one vector of its source span to a unique positive target
basis vector. The absolute global group `R_G(F, 0)` of Henniart 2.5 is not
in the Library and remains with the global definition owners.

### 1.3 Norm-one vectors and genuine positive basis elements

| Module | Declarations | Original source | Status |
| --- | --- | --- | --- |
| `VirtualRepresentation/DescentStatement` | `IntegralNormOneSignedBasisStatement`, `IntegralPositiveDegreeBasisStatement`, `IntegralIsometrySignedBasisStatement`, `IntegralIsometryPositiveBasisStatement` | Henniart 2000 §2.8, p.448 | Proved (above) |
| `VirtualRepresentation/Supercuspidal/PositivityStatement` | `Langlands.VirtualRepresentation.Supercuspidal.{UnitarySignedBasisStatement, UnitaryPositiveBasisStatement, UnitaryNormOneExtractionStatement}` | Henniart 2000 §§2.5–2.6, pp.445–447 | Unproved |

The supercuspidal unit works in the published lattice
`PadicSupercuspidal.UnitaryLattice`, free on actual unitary supercuspidal
classes of all ranks; the target is not the group on all irreducible classes of
`GL_n`. Its degree `PadicSupercuspidal.unitaryDegree` weights a class of
`GL_n(F)` by the group rank `n`, never by the dimension of a smooth carrier.

### 1.4 Finite-order determinant and unramified-twist reductions

| Module | Declarations | Original source | Status |
| --- | --- | --- | --- |
| `Weil/Representation/Structure` (parameter task `ce2095a8-9814-480e-ac62-bd2f27fa88ae`) | `Langlands.Weil.{UnramifiedReduction, FiniteImageExtension, RepresentationStructure}` | Henniart 1980 §§2.1–2.6; Tate (1979) §2.2 | Proved: `Langlands.Weil.unramifiedReduction`, `Langlands.Weil.finiteImageExtension`, `Langlands.Weil.representationStructure` |
| `Correspondence/HenniartStableMapStatement` (this task) | `Langlands.Henniart.{UnramifiedTwistIndependenceStatement, HenniartConstructionStatement}` | Henniart 2000 §4.4; Henniart 1993 §§4.2–4.4 | Unproved |

This task does not restate the intrinsic Weil reductions; it states their
application: independence of the chosen unramified twist and the extension of
the stable map to all irreducible classes.

### 1.5 Central-character and conductor finiteness

| Module | Declarations | Original source | Status |
| --- | --- | --- | --- |
| `Representation/Category/ClassInvariants`, `Representation/Conductor/ClassLevel` | class-level central characters and fixed vectors, `Langlands.SmoothDualClass.firstFixedLevel` and their invariance laws | JPSS 1981 §5.1 | Definitions with proved laws |
| `Representation/Classification/SupercuspidalStrata` | `Langlands.GeneralLinear.SupercuspidalClass.{firstFixedLevel, centralLevelStratum, …}` | Bernstein–Zelevinsky 1976 Cor. 4.15, p.41; JPSS 1981 §5.1, p.211 | Definitions with proved laws |
| `Correspondence/SupercuspidalFinitenessStatement` | `Langlands.Henniart.{SupercuspidalCompactOpenFinitenessStatement, SupercuspidalBoundedLevelFinitenessStatement, SupercuspidalLevelFinitenessReductionStatement, SupercuspidalFinitenessStatement}` | Bernstein–Zelevinsky 1976 Cor. 4.15 and §3.1 | Reduction proved: `supercuspidalLevelFinitenessReduction`; `SupercuspidalFinitenessStatement` conditional on compact-open finiteness (`Correspondence/SupercuspidalLevelFinitenessProof`) |
| `Correspondence/HenniartStableMapStatement` (this task) | `Langlands.Henniart.SupercuspidalEpsilonConductorFinitenessStatement` | Henniart 2000 §4.3 (the set `P`); Henniart 1988 §2.5 | Unproved |

`firstFixedLevel : WithTop ℕ` is the newvector level. Its identification with
the epsilon conductor is the separate statement
`Langlands.Conductor.ConductorExponentStatement`
(`Representation/Conductor/EssentialStatement`, Worker 11).

### 1.6 Finite separating tests from the local converse

| Module | Declarations | Original source | Status |
| --- | --- | --- | --- |
| `Correspondence/SupercuspidalFiniteEpsilonStatement` (Worker 78) | `Langlands.Henniart.{FiniteSupercuspidalEpsilonSeparationStatement, SupercuspidalStratumEpsilonSeparationStatement, FiniteSupercuspidalEpsilonLiftingStatement, SupercuspidalFiniteEpsilonStatement}` | Henniart 1993 §1.1 and Corollary, pp.339–340, Thm 4.1, p.348; Henniart 2000 §4.3 | Lifting proved: `finiteSupercuspidalEpsilonLifting`; the other three conditional on `Langlands.RankinSelberg.SupercuspidalLocalConverseStatement` (`Correspondence/SupercuspidalFiniteEpsilonProof`), and they close by composition (below) |

The local converse theorem is Worker 11's
`Representation/RankinSelberg/LocalConverseStatement`; this task consumes it.
It is proved, for all universes and without hypotheses, by
`Langlands.RankinSelberg.supercuspidalLocalConverse`
(`Representation/RankinSelberg/SupercuspidalLocalConverseProof`, Worker 1718).
Hence the term
`Langlands.Henniart.supercuspidalFiniteEpsilon_of_localConverse
Langlands.RankinSelberg.supercuspidalLocalConverse` proves
`SupercuspidalFiniteEpsilonStatement`, and the two separation statements close
in the same way through `finiteSupercuspidalEpsilonSeparation_of_localConverse`
and `supercuspidalStratumEpsilonSeparation_of_finiteSeparation`. These three
compositions were compile-checked against the commit above.

### 1.7 Enlargement of auxiliary extensions and finite counting

| Module | Declarations | Original source | Status |
| --- | --- | --- | --- |
| `Correspondence/FiniteAuxiliaryStatement` (legacy re-export `Henniart/FiniteAuxiliaryStatement`) | `Langlands.Henniart.{FiniteSeparationStatement, FiniteTestLiftingStatement, FiniteLiftedSeparationStatement, FiniteGaloisEnlargementStatement, FiniteCountingStatement, FiniteOrbitCountingStatement, FiniteAuxiliaryStatement}` | Henniart 2000 §4.3, pp.452–453; Henniart 1988 §2.8, pp.506–507 (generic elementary form) | Proved: `Langlands.Henniart.finiteAuxiliary` (`Correspondence/FiniteAuxiliaryProof`) |
| `Global/Arithmetic/HenniartGlobalizationStatement` (H3) | `Langlands.Global.{RelativeGaloisGlobalization, HenniartGlobalizationStatement}` | Henniart 2000 Thm 3.1, p.448 | Unproved |
| `Global/Factors/HenniartCompositeMapStatement` (H3) | `Langlands.Correspondence.LatticeMap.HenniartProperties`; `Langlands.Global.PoleComparison.{HenniartCompositeOperationStatement, HenniartCompositeFactorStatement, HenniartCompositeMapStatement}` | Henniart 2000 §§3.7–3.8, p.451 | Unproved |

### 1.8 Choice independence and the rank induction

All in `Correspondence/HenniartStableMapStatement` (this task), main declaration
`Langlands.Henniart.HenniartStableMapStatement`, helpers in
`Langlands.Henniart.StableMap`. Sources: Henniart 2000 §§4.1–4.4 with
Théorème 4.2, pp.452–453; Henniart 1993 §4.

| Declaration | Content | Status |
| --- | --- | --- |
| `StableMap.IsCandidate` | a lattice equivalence whose domain contains every unitary class factoring through a finite quotient `q` and which satisfies `LatticeMap.HenniartProperties` | Definition |
| `StableMap.IsStableImage` | for one such `q`, a candidate exists and all candidates at `q` agree on `σ` | Definition |
| `StableMap.StableExistsAt`, `StableMap.StableSurjectiveAt`, `StableMap.RankStage` | the two assertions of the induction in rank `n` | Definitions |
| `CandidateExistenceStatement` | every finite quotient has a candidate (local form of Thm 3.1 with §§3.7–3.8) | Unproved |
| `ChoiceIndependenceStatement` | Thm 4.2 (a) | Unproved |
| `RankOneStageStatement` | base case `n = 1` | Unproved |
| `ChoiceIndependenceStepStatement` | for `n > 1`, all lower `RankStage` imply `StableExistsAt n` | Unproved |
| `SurjectivityStepStatement` | `StableExistsAt n` implies `StableSurjectiveAt n` | Unproved |
| `RankInductionStepStatement` | for `n > 1`, all lower `RankStage` imply `RankStage n` | Unproved |
| `StableCorrespondenceStatement` | `RankStage n` for every `n` | Unproved |

Candidates replace Henniart's "constructions of §3" by every local map with the
properties of 3.8. This is stronger than the printed 4.2 (a) and is what the
proof in §4.3 uses; the H3 statements show that the composite maps are
candidates under their hypotheses. The lower-rank stages, including lower-rank
surjectivity used to lift the separating tests, are explicit hypotheses of the
steps.

### 1.9 The numerical correspondence and orbit counting

All in `Correspondence/HenniartNumericalStatement` (this task), main declaration
`Langlands.Henniart.NumericalCorrespondenceStatement`, helpers in
`Langlands.Henniart.Numerical`. Sources: Henniart 1988 §§1.1–1.2, Théorème
1.2, pp.497–498, §2.8, pp.506–507; Henniart 2000 §1.3 and §4.3; JPSS 1981
Théorème 5.1.

| Declaration | Content | Status |
| --- | --- | --- |
| `Numerical.HasArtinConductor` | the Artin conductor through an actual finite inertia presentation of a representative | Definition |
| `Numerical.conductor` | `firstFixedLevel` of a supercuspidal class | Definition |
| `Numerical.weilUnramifiedTwist`, `Numerical.supercuspidalUnramifiedTwist` | twists by `z ∈ ℂˣ`: geometric Frobenius ↦ `z`; `g ↦ z^(ord det g)` | Definitions |
| `Numerical.IsNumericalInjection` | injective, conductor-preserving, twist-compatible | Definition |
| `Numerical.weilOrbitStratum`, `Numerical.supercuspidalOrbitStratum` | unramified-orbit classes of fixed rank containing a class of conductor `a` | Definitions |
| `NumericalInjectionExistenceStatement` | Thm 1.2, existence | Unproved |
| `NumericalSurjectivityStatement` | Thm 1.2, every such injection is surjective | Unproved |
| `NumericalOrbitCountStatement` | both orbit strata finite, with equal `Set.ncard` | Unproved |
| `NumericalOrbitReductionStatement` | orbit counts and finite target conductors imply surjectivity | Unproved |

The counting statement compares finite strata, never two infinite
cardinalities. The generic counting step is the proved
`FiniteOrbitCountingStatement` of section 1.7.

## 2. Exact versions

First twelve hexadecimal digits of the SHA-256 of each file at Library commit
`5263a53b575d66cc4ebc5364c0d990d1b111c7f7`.

| Module | `.lean` | `.md` |
| --- | --- | --- |
| `Representation/Finite/CharacterStatement` | `d67728269f1f` | `7a6a6b87f146` |
| `Representation/Finite/CharacterTheoryProof` | `6ced9b52acbc` | `0b52023adc8b` |
| `Representation/Finite/BrauerStatement` | `b5f0c11fe40d` | `196495fefa55` |
| `Representation/Finite/BrauerTheoryProof` | `3a29a4e214c4` | `a2b89e0a0d7c` |
| `Representation/Finite/BrauerLatticeProof` | `2ca09d77b2b6` | `f98e44c0f535` |
| `Representation/Finite/DegreeZeroBrauerStatement` | `ffa521a51f07` | `0db7e5006cf3` |
| `Representation/Finite/DegreeZeroBrauerProof` | `a339b1e4b3b8` | `9e20cdf5834d` |
| `VirtualRepresentation/Weil/FiniteQuotientStatement` | `796ddf89325f` | `88f65bf3d982` |
| `VirtualRepresentation/DescentStatement` | `1efb947b492c` | `50b7c5c10528` |
| `VirtualRepresentation/DescentProof` | `eaf13753ff65` | `ff6723c8a88d` |
| `VirtualRepresentation/Supercuspidal/PositivityStatement` | `b029a6b354cb` | `78cabf20fd6f` |
| `Global/Factors/RelativePolePairingStatement` | `b815b1c7ca25` | `37f7aa89ced3` |
| `Global/Factors/RelativePolePairingProof` | `7ce2a830390c` | `47dc7cbb2339` |
| `Global/Factors/RelativeIsometryOperationStatement` | `9d12e7e2f239` | `b2c3c35fad5d` |
| `Global/Factors/RelativeIsometryFactorStatement` | `5b769806a3cc` | `552787747a2e` |
| `Global/Arithmetic/HenniartGlobalizationStatement` | `f8004a0c7ce1` | `70c8e4c96376` |
| `Global/Factors/HenniartCompositeMapStatement` | `486f1396356c` | `475e1733db98` |
| `Weil/Representation/Structure` | `c692c4ee4aa3` | `ee54cfd7eeb0` |
| `Weil/Representation/StructureProof` | `2cdf064f95c2` | `5adf46afbca8` |
| `Representation/Category/ClassInvariants` | `4f65d38d1309` | `058f7fbcfcec` |
| `Representation/Conductor/ClassLevel` | `20a57100f00c` | `2dabad5a856a` |
| `Representation/Classification/SupercuspidalStrata` | `fe7fddcd7c5c` | `c87c5cceec8c` |
| `Correspondence/SupercuspidalFinitenessStatement` | `889dd8cbdc4e` | `bda0803a57e7` |
| `Correspondence/SupercuspidalLevelFinitenessProof` | `37a31601a033` | `2cf272e55693` |
| `Correspondence/SupercuspidalFiniteEpsilonStatement` | `91d6f303dcb4` | `4531c2d9e64c` |
| `Correspondence/SupercuspidalFiniteEpsilonProof` | `589792b14c26` | `7f705f7c071c` |
| `Correspondence/FiniteAuxiliaryStatement` | `24f6ee46420d` | `5959830011cd` |
| `Correspondence/FiniteAuxiliaryProof` | `e72c6cfecb21` | `d2eeeba3a882` |
| `Representation/Conductor/EssentialStatement` | `5a251747b335` | `04d8ea739455` |
| `Representation/RankinSelberg/LocalConverseStatement` | `c8f1100f4b74` | `5a50f7adeaa1` |
| `Representation/RankinSelberg/SupercuspidalLocalConverseProof` | `c06ce6c186d0` | `a845b074cd74` |
| `Correspondence/SupercuspidalFactorCompatibility` | `28f432e159f2` | `63e608f7ece4` |
| `Correspondence/SupercuspidalEpsilonComparison` | `73f5ce4f1720` | `9da41f034ddd` |
| `Correspondence/SupercuspidalSpecification` | `b40cc87cb82b` | `5ceea3448e69` |
| `Correspondence/HenniartNumericalStatement` (artifact `923c69a6-1ab7-4b0a-83df-40c7226637bb`) | `36ee89946db5` | `0300b95ac419` |
| `Correspondence/HenniartStableMapStatement` (artifact `35a44b39-88c7-4087-9604-41516fd62593`) | `ccb905fc61f1` | `18455e8e986d` |

## 3. Retained source gaps

- Henniart 1988, Théorème 1.3 (the explicit count `C_K(n, j)`) is not stated.
  Its source chain uses Koch 1984, Satz 1, which the operator declined to
  supply; the discrepancy in the summation range of H1988 §1.3 for Swan
  conductor zero is unresolved. The orbit-count statement of section 1.9 is a
  sufficient formulation that needs neither.
- The numerical theorem is stated for p-adic fields only, the case Henniart
  2000 uses; Henniart 1988 covers every local field.
- The H3 units are finite-relative and witnessed; the absolute-global objects
  of Henniart 2.5 remain with the global definition owners.
- Worker 78's tests use `RankinSelberg.IsClassEpsilonFactor`; `HenniartProperties`
  and `SupercuspidalEpsilonConductorFinitenessStatement` use
  `Correspondence.IsSupercuspidalPairEpsilonFactor`. The Markdown of
  `HenniartStableMapStatement` lists their comparison as a retained
  obligation, but it is already met:
  `Langlands.Correspondence.isSupercuspidalPairEpsilonFactor_iff_class`
  (`Correspondence/SupercuspidalEpsilonComparison`, Worker 357) proves the two
  relations equivalent, evaluated at the same nontrivial character and Haar
  measure, whenever the first class has rank at least that of the second. The
  tests used by `ChoiceIndependenceStepStatement` pair a class of rank `n` with
  classes of lower rank, so the equivalence applies to all of them.
- That a supercuspidal class with finite-order central character is unitary is
  not asserted.

## 4. Delegated and consumed responsibilities

| Input | Owner | Use here |
| --- | --- | --- |
| Intrinsic Weil reductions | parameter task `ce2095a8-9814-480e-ac62-bd2f27fa88ae` | section 1.4 |
| Local converse, pair factors, epsilon conductor | Worker 11 (`RankinSelberg`, `Conductor` statements); JPSS constructions with their owners | sections 1.5–1.6 |
| Weak association, relative pole comparison, globalization, composite map | H1 task `205503d3-82c7-4b1a-a4f0-90d02bbe9a2e`; H3 task `34b81620-20d7-4059-9b08-6bedd1c1c029`; global statement task `91266440-3276-48dc-ab77-8d1c1fa386e8` | sections 1.2, 1.7 |
| Extension to all Weil–Deligne parameters, uniqueness | final LLC assembly | consumes `HenniartConstructionStatement` and `SupercuspidalCorrespondenceStatement` |

The unproved targets in section 1 are separate proof obligations. Their own
Markdown lists the inputs each proof needs.
