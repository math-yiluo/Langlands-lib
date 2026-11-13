# Local Langlands for GL_n: published reductions and the remaining premises

Author: Worker 0, for Task 0 (`69dd20b3-6a77-44aa-b779-32391843c8dd`). First
version 10 November 2026, second version 11 November 2026, third, fourth and
fifth versions 12 November 2026. This sixth version, of 13 November 2026, was
checked against Library commit `ed924aef420de137b4cbaa3b063a3618afcd73fd`.

This note records how the published Library reduces the full local Langlands
correspondence for GL_n to six propositions, and names the task that owns
each of them. The newest published reduction,
`Henniart.Extension.supercuspidalCorrespondenceHenniartRankOneInputs`,
discharges normalized local reciprocity on the common closure with the
Library's proof, as the fifth version's composite did. It also replaces Tate's
spectral conductor formula, one of the fifth version's five open premises, by
two narrower statements about conductors. Six premises therefore remain open.
The composite Lean module below assembles the published theorems. It has been
compiled as a development check but is not published. Each of the six open
propositions still needs an accepted `lean.proof@1` candidate. For statement
meanings and sources see
[the specification coverage note](llc-specification-coverage.md); this note
does not restate them.

## The target

`Langlands.Correspondence.FullCorrespondenceStatement.{uF, uP, uA}` (module
`Correspondence/FullSpecification`, proof task Task 4809,
`1ccfc228-cd00-4744-b7c2-42b1affdcf69`). The universes are those of the
p-adic field, the parameter carriers and the representation carriers.

## Published: the full correspondence from the supercuspidal one

Paths below are relative to `Langlands/`.

The published theorem
`Correspondence.fullCorrespondenceStatement_of_supercuspidalCorrespondence`
(module `Correspondence/FullCorrespondenceReduction`, Task 4809) proves
`FullCorrespondenceStatement.{uF, uP, uA}` from
`SupercuspidalCorrespondenceStatement.{uF, uP, uA}`. It uses only the existence
part of its hypothesis. Every other ingredient is a published proof: conditional
assembly (Henniart 2002, Thm 1.5), the L-factor characterization of assembly
(Thm 1.8), supercuspidal extension (Cor. 1.6), the supercuspidal local converse
theorem, the L-factor characterization of supercuspidal classes, the multisegment
head classification, the pole-order characterization of square-integrable
classes and the uniqueness of local constants. The module's Markdown lists them
by Lean name. Task 4806's published `Correspondence.fullCharacterization`
(`Correspondence/FullCharacterizationProof`) proves Henniart 2002, Cor. 1.8, on
its own as well.

## Published: Henniart's construction of the supercuspidal correspondence

Published theorems by Worker 4803 (Task 4803,
`871c9ea7-1e86-44f8-bba0-6aa26b3ef474`) prove
`SupercuspidalCorrespondenceStatement.{uK, uW, uV}`, existence and uniqueness,
from hypotheses. In the full correspondence the universes are `uK = uF`,
`uW = uP` and `uV = uA`. The fifth version of this note was based on the
fourth theorem below, whose six premises are:

- (S1) candidate existence, `Henniart.CandidateExistenceStatement`;
- (S2) normalized local reciprocity,
  `LocalClassField.CommonClosureReciprocityExistence`;
- (S3) local constants for every normalized family,
  `LocalFactor.NonabelianSystem.Exists`;
- (S4) numerical surjectivity, `Henniart.NumericalSurjectivityStatement`
  (Henniart 1988, Thm 1.2);
- (S5) Tate's spectral conductor formula,
  `LocalFactor.ConductorExponent.SpectralConductorStatement` (Tate 1979,
  (3.4.5); Deligne 1973, (5.5.2));
- (S6) the conductor exponent of generic representations,
  `Conductor.ConductorExponentStatement` (Jacquet–Piatetski-Shapiro–Shalika
  1981, Thm (5.1)).

The theorems are:

- `Henniart.Extension.supercuspidalCorrespondenceHenniartInduction` (module
  `Correspondence/HenniartCorrespondenceInduction`) carries out Henniart's
  induction on the rank (Henniart 2000, §4.3) from five propositions: candidate
  existence, the surjectivity step `Henniart.SurjectivityStepStatement`, the
  finiteness of candidate sets
  `Henniart.SupercuspidalEpsilonConductorFinitenessStatement`, normalized local
  reciprocity and the existence of local constants.
- `Henniart.Extension.supercuspidalCorrespondenceHenniartFinal` (module
  `Correspondence/HenniartCorrespondenceFinal`) applies the first theorem after
  replacing the surjectivity step and the finiteness of candidate sets by their
  own inputs. It assumes eight propositions: S1–S6,
  `Henniart.SupercuspidalCompactOpenFinitenessStatement.{uK, uV}` and
  `RankinSelberg.EqualRankEpsilonCharacterChangeStatement.{uK, uV, 0}`.
- `Henniart.Extension.supercuspidalCorrespondenceHenniartSevenInputs` (module
  `Correspondence/HenniartCorrespondenceSevenInputs`) applies the second
  theorem with `RankinSelberg.equalRankEpsilonCharacterChange` (module
  `Representation/RankinSelberg/EqualRankEpsilonCharacterChangeProof`), which
  proves `EqualRankEpsilonCharacterChangeStatement` at every universe level. It
  assumes seven propositions: S1–S6 and
  `Henniart.SupercuspidalCompactOpenFinitenessStatement.{uK, uV}`.
- `Henniart.Extension.supercuspidalCorrespondenceHenniartSixInputs` (module
  `Correspondence/HenniartCorrespondenceSixInputs`) applies the first theorem
  directly. It obtains the pair epsilon exponent statement from
  `equalRankEpsilonCharacterChange`, the surjectivity step as the second
  theorem does, and the finiteness of candidate sets from a reduction that
  needs no finiteness premise (the fifth reduction below). It assumes S1–S6.
- `Henniart.Extension.supercuspidalCorrespondenceHenniartRankOneInputs`, the
  fifth theorem, applies the fourth; see the next section.

The second to fourth theorems use five published reductions:

- `Henniart.Extension.surjectivityStepReduction` (module
  `Correspondence/HenniartSurjectivityStepProof`) derives the surjectivity
  step from S1–S6 and
  `RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0}`. It extends the
  stable rank-n images by unramified twists (Henniart 2000, §4.4) to a map that
  is injective, commutes with unramified twists and preserves conductors, and
  then applies the numerical surjectivity S4 (Henniart 1988, Thm 1.2).
- `Henniart.Extension.supercuspidalEpsilonConductorFinitenessReduction`
  (module `Correspondence/HenniartConductorFinitenessProof`) derives the
  finiteness of candidate sets from
  `Henniart.SupercuspidalBoundedLevelFinitenessStatement.{uK, uV}`, the pair
  epsilon exponent statement and S6.
- `Henniart.supercuspidalLevelFinitenessReduction` (module
  `Correspondence/SupercuspidalLevelFinitenessProof`) derives that bounded-level
  finiteness from `Henniart.SupercuspidalCompactOpenFinitenessStatement`.
- `RankinSelberg.pairEpsilonExponentReduction` (module
  `Representation/RankinSelberg/PairEpsilonExponentProof`) derives
  `PairEpsilonExponentStatement` (Bushnell–Henniart–Kutzko 1998, introduction)
  from `EqualRankEpsilonCharacterChangeStatement`, which
  `equalRankEpsilonCharacterChange` proves. The unequal-rank case comes from
  the published `RankinSelberg.pairFactorCharacterChange`.
- `Henniart.Extension.supercuspidalEpsilonConductorFinitenessPadicReduction`
  (module `Correspondence/HenniartPadicConductorFinitenessProof`) derives the
  finiteness of candidate sets from the pair epsilon exponent statement and
  S6 alone. Henniart's candidate sets involve only p-adic fields, and
  over them bounded-level finiteness is proved:
  `Henniart.CompactOpenFiniteness.centralLevelStratum_finite` (module
  `Correspondence/PadicSupercuspidalFinitenessProof`) is the p-adic case of
  Bernstein–Zelevinsky 1976, Cor. 4.15, in bounded-level form.

## Published: the six-premise entry

Worker 4803 (Task 4803) published the fifth theorem, recorded in the shared
planning graph as candidate `5ab85077-a08d-471e-99ea-ef0d26655e22`:

- `Henniart.Extension.supercuspidalCorrespondenceHenniartRankOneInputs`
  (module `Correspondence/HenniartCorrespondenceRankOneInputs`) proves
  `SupercuspidalCorrespondenceStatement.{uK, uW, uV}` from the six propositions
  in the table below. It applies `supercuspidalCorrespondenceHenniartSixInputs`
  with two of that theorem's premises discharged:
  - S2, normalized local reciprocity, by the published
    `LocalClassField.commonClosureReciprocityExistence` (module
    `ClassFieldTheory/Local/CommonClosureExistenceProof`; artifact
    `9119eeeb-d405-41b5-bdb8-9997f722b114`, by Worker 125 for Task 4919);
  - S5, Tate's spectral conductor formula, by the published reduction
    `LocalFactor.SpectralConductor.spectralConductorRankOneReduction` (module
    `LocalFactor/SpectralConductorReduction`). For every p-adic field `F`, this
    reduction derives the formula from premises 4 and 5 of the table:
    refinement invariance of presentation conductors and rank-one conductor
    transport in the common closure. Its proof also uses the published
    degree-zero generation `commonClosureDegreeZeroGeneration` and the
    induction identity `conductorFunctional_induce_eq` (module
    `LocalFactor/SpectralConductorInduction`; Serre 1979, VI §2, Prop. 4).

## The six open premises

The table lists the six premises of
`supercuspidalCorrespondenceHenniartRankOneInputs` in its order, at the
universes of the full correspondence (`uK = uF`, `uW = uP`, `uV = uA`). None
has a Library proof at commit `ed924aef`.

The owners and states below are TaskHub task records as inspected on
13 November 2026; they are not part of the Library commit. Worker 0 published
Tasks 5583 and 5584 on 11 November, Task 5737 on 12 November and Task 5815 on
13 November 2026. On 13 November 2026 these four tasks were ready with no
executor.

| # | Premise (universes of the full correspondence) | Module | Owner and state on 13 November 2026 |
| --- | --- | --- | --- |
| 1 | `Henniart.CandidateExistenceStatement.{uF, uP, uA, uP, uF}` (Henniart 2000, Thm 3.1 with §§3.7–3.8) | `Correspondence/HenniartStableMapStatement` | Task 5583 `54bed1a5-c9db-4be3-b59b-e4eb4abb89b8`, ready, no executor. Its contract expects a route through the global program of Task 3657 (`34b81620-20d7-4059-9b08-6bedd1c1c029`). |
| 2 | `∀ p K eC, LocalFactor.NonabelianSystem.Exists.{uF, uP} K eC` | `LocalFactor/NonabelianSystem` | Task 4913 `2ee1672e-11b3-4c27-8959-d9b1957ab12d`, waiting; its executor is Worker 4913. |
| 3 | `Henniart.NumericalSurjectivityStatement.{uF, uP, uA}` (Henniart 1988, Thm 1.2) | `Correspondence/HenniartNumericalStatement` | Task 5584 `35ad7726-c0bc-499a-ba29-69e4bc6e3c2a`, ready, no executor. |
| 4 | `∀ p K A, Ramification.Padic.FiniteInertiaConductorRefinementStatement.{uF, max uF uP} K A`, for `A : FiniteRepresentation.{0, uF, max uF uP} ℂ (localWeilGroup K)` (Serre 1979, IV §3 and VI §2, Prop. 3) | `LocalFactor/Ramification/InertiaPresentationStatement` | Task 5737 `867d5dff-b37c-4c7e-a3e8-c0286f83531b`, ready, no executor. |
| 5 | `∀ p K, LocalFactor.SpectralConductor.CommonClosureRankOneConductorStatement.{uF} K` (Serre 1979, XV §2, Thm 1 and Cor. 2–3; VI §2, Prop. 5) | `LocalFactor/SpectralConductorRankOneStatement` | Task 5815 `cbf11cf8-6abd-4db5-a59b-7b47c5b26585`, ready, no executor. |
| 6 | `Conductor.ConductorExponentStatement.{uF, uA}` (Jacquet–Piatetski-Shapiro–Shalika 1981, Thm (5.1)) | `Representation/Conductor/EssentialStatement` | Task 5032 `7b8711bf-90dc-40ae-923e-5bfecc3550b6`, claimed; its executor Worker 5032 was working. It is the second conjunct of that task's target `Conductor.EssentialConductorStatement`. |

Premise 4 says that enlarging the finite Galois field of a finite-inertia
presentation of a Weil representation does not change its Artin and Swan
conductor sums. It is clause 6 of
`Ramification.Padic.InertiaSurjectivityPresentationAndConductorIndependenceStatement`.
Task 5676 (`b1cfcfb8-bef5-4a1f-ad85-7c0c1c45d5bd`) has that whole statement as
its target.

Premise 5 says that, at an intermediate field `L` of the common closure, the
Artin sum of an inertia character of a finite Galois `M/L` equals the
multiplicative conductor of the character of `L^×` attached by the supplied
normalized reciprocity family to an agreeing character of `W_L`. Task 5815's
contract forbids unproved Library propositions as premises. Its suggested route
uses only proved Library results:

- `LocalClassField.absoluteUpperReciprocityTheorems` (module
  `ClassFieldTheory/Local/AbsoluteReciprocityProof`, by Worker 5168) proves
  `AbsoluteUpperReciprocityTheorems.{u}`, the absolute upper-numbering form of
  local reciprocity with the conductor levels of quasicharacters (Serre 1979,
  XV §2);
- `LocalClassField.finiteUpperReciprocityTheorems` (module
  `ClassFieldTheory/Local/UpperReciprocityProof`) proves the finite version;
- `Ramification.HerbrandBridge.absoluteUpperFiniteImage` (module
  `LocalFactor/Ramification/Herbrand/AbsoluteProof`) proves that absolute upper
  ramification groups map onto those of every finite Galois subfield;
- `LocalClassField.commonClosureGeometricProof` (module
  `ClassFieldTheory/Local/CommonClosureGeometricProof`) compares a normalized
  family with standalone geometric reciprocity.

The alternative route through finite abelian conductor transport
(`LocalClassField.FiniteCharacterConductorTheorems`, Task 5738,
`cbe92f65-9440-440c-93e1-9817d4aa300f`) and inflation of conductors
(`Ramification.Padic.FiniteGaloisConductorInflationStatement`, Task 5739,
`1e35eaa4-0bf9-4e1f-b16f-cc202c9d3b3a`) can be used only after those proofs are
published.

## Tasks that left the route

The fifth version of this note listed `∀ p K,
ConductorExponent.SpectralConductorStatement.{uF, uP} K` as its fifth premise,
owned by Task 5626 (`24b84ed8-5c32-460b-b50b-30a1c08fb408`). The published
`spectralConductorRankOneReduction` derives it from premises 4 and 5, so the
route no longer needs Task 5626 on its own. The same holds for the conductor
laws that Task 5626's suggested route needed: Task 5651
(`62ccf2f8-9d7b-4b62-bb2f-231ce16e1916`, additivity in short exact sequences)
and Task 5661 (`32abafa4-2d05-4dab-9a1f-d0b58dcdc86e`, conductors of induced
representations). Of the four conductor clauses of Task 5676's target that
the Library does not prove, the route uses only clause 6, which is Task 5737's
target on its own. These statements remain the targets of their tasks; this
note does not record those tasks' current state.

The fourth version listed
`Henniart.SupercuspidalCompactOpenFinitenessStatement.{uF, uA}`
(Bernstein–Zelevinsky 1976, Cor. 4.15, printed p. 41, in compact-open form),
owned by Task 5585 (`5da7d945-39ed-4dcb-ace6-030fa18e4f24`), and the third
version listed `RankinSelberg.EqualRankEpsilonCharacterChangeStatement.{uF, uA, 0}`,
owned by Task 5590 (`8c1da9ec-76db-4f6c-97c6-c015c3b3bb39`). Worker 4803 proved
the p-adic case of the first
(`Henniart.CompactOpenFiniteness.padicSupercuspidalCompactOpenFiniteness`),
which is the only case the route uses, and the second
(`RankinSelberg.equalRankEpsilonCharacterChange`), as described above. The
Library statement of the first quantifies over every nonarchimedean local
field, including fields of positive characteristic, and remains Task 5585's
target.

## The composite

The module below compiles at commit
`ed924aef420de137b4cbaa3b063a3618afcd73fd` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with 0 errors and 0 warnings. The
check compiled the block verbatim as a private draft module in the Lean
service; its diagnostics are private records. To reproduce it, save the block
as a draft module and compile it with `lean_check`. A second draft module that
imports it and runs `#print axioms` on
`fullCorrespondence_of_henniartRankOneInputs` reports only the axioms
`propext`, `Classical.choice` and `Quot.sound`. Both theorems it applies are
published: `fullCorrespondenceStatement_of_supercuspidalCorrespondence` and
`supercuspidalCorrespondenceHenniartRankOneInputs`. Its hypotheses are the six
open premises, in the order of the table. The fifth version's composite,
`fullCorrespondence_of_henniartFiveInputs`, assumed Tate's spectral conductor
formula in place of premises 4 and 5.

```lean
import Langlands.Correspondence.FullCorrespondenceReduction
import Langlands.Correspondence.HenniartCorrespondenceRankOneInputs

namespace Langlands.Correspondence

universe uF uP uA

open Langlands.Henniart LocalFactor LocalFactor.CommonClosure in
/-- The full correspondence from the six open premises of
`supercuspidalCorrespondenceHenniartRankOneInputs`. -/
theorem fullCorrespondence_of_henniartRankOneInputs
    (hCE : CandidateExistenceStatement.{uF, uP, uA, uP, uF})
    (hsys : ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uF} p) (eC : ReciprocityFamily K),
      NonabelianSystem.Exists.{uF, uP} K eC)
    (hnum : NumericalSurjectivityStatement.{uF, uP, uA})
    (href : ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uF} p)
      (A : FiniteRepresentation.{0, uF, max uF uP} ℂ (Weil.Local.localWeilGroup K)),
      Ramification.Padic.FiniteInertiaConductorRefinementStatement.{uF, max uF uP} K A)
    (hR : ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uF} p),
      SpectralConductor.CommonClosureRankOneConductorStatement K)
    (hJPSS : Conductor.ConductorExponentStatement.{uF, uA}) :
    FullCorrespondenceStatement.{uF, uP, uA} :=
  fullCorrespondenceStatement_of_supercuspidalCorrespondence
    (Extension.supercuspidalCorrespondenceHenniartRankOneInputs.{uF, uP, uA}
      hCE hsys hnum href hR hJPSS)

end Langlands.Correspondence
```

## Statements off this route

The specification coverage note lists two statements without a Library proof
that the reduction above does not use:
`Correspondence.AssemblyExtendsStatement` (module
`Correspondence/AssemblyRelation`), for which Worker 0 published proof Task 5627
(`122f660e-fb61-4873-975a-bbcbcafa8ec5`) on 12 November 2026, and
`Correspondence.FullCorrespondenceRestrictionStatement` (module
`Correspondence/FullSpecification`), which had no task on 12 November 2026.

## Duplicate declaration names: resolved

The first version of this note recorded that a composite import failed because
published modules declared the same instance names without importing each
other, for example `Langlands.Correspondence.instTopologicalSpaceCarrier_5`.
Task 5265 (`2e9349b0-20cd-4720-8229-cc98f746dcb8`) renamed the repeated
declarations; the renames have been in the Library since commit
`3f9691717b5fba9a8561abf028ae957f63bdf0dd`. Its scan is described in
`Langlands/Correspondence/AssemblyLCharacterizationReduction.md`, section "How
the names were checked". The composite above compiles without private renamed
copies.
