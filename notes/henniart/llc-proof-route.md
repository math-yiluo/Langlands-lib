# Local Langlands for GL_n: published reductions and the remaining premises

Author: Worker 0, for Task 0 (`69dd20b3-6a77-44aa-b779-32391843c8dd`). First
version 10 November 2026, second version 11 November 2026, third, fourth and
fifth versions 12 November 2026, sixth to thirteenth versions 13 November
2026, fourteenth version 14 November 2026. This fifteenth version, also of
14 November 2026, was checked against Library commit
`f676fad71e1679d672d3e20560dc814d4e1f8ffd`.

This note records how the published Library reduces the full local Langlands
correspondence for GL_n to three propositions, and names the task that owns
each of them. The newest published reduction of the supercuspidal
correspondence, `Henniart.Extension.supercuspidalCorrespondenceHenniartThreeInputs`,
has exactly these three premises. It applies the five-premise
`Henniart.Extension.supercuspidalCorrespondenceHenniartFiveInputs` and supplies
the other two premises from published proofs: the existence of local
constants, by `LocalFactor.NonabelianSystem.exists_system`, and rank-one
conductor transport in the common closure, by
`LocalFactor.SpectralConductor.commonClosureRankOneConductor`. The first
theorem of the composite Lean module below combines it with the published
passage from the supercuspidal to the full correspondence. The module has
been compiled as a development check but is not published. Each of the three
open propositions still needs an accepted `lean.proof@1` candidate.

The Library also proves a reduction of the first premise, candidate
existence, to five global inputs: `Henniart.candidateExistenceReduction`. It
gives candidate existence only with the automorphic-lattice universe equal to
`0`. One of the five inputs, local relative class formation, is proved. So
the composite module has a second theorem. It proves the full correspondence
with representation universe `0` from the four other global inputs and
premises 2 and 3. Premise 1 below names the tasks that own those four inputs;
all four have proof tasks.

Since the fourteenth version, the Library has published a reduction
statement for the first of these inputs, Harris's Prop. 4.8:
`Global.Harris.Proposition48ReductionStatement` says that fourteen named
propositions together imply it. Neither the reduction nor any of its
fourteen inputs has a Library proof. Three of the inputs have their own
proof tasks, and two planning tasks cover four more. A TaskHub search found
no proof task for the reduction itself or for the other seven inputs; the
planning task that stated them is to publish those tasks. For the third
premise, the two propositions about unramified principal series that its
owner task published as proof tasks are now proved. The three open premises
are unchanged. For statement meanings and sources see
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
  fifth theorem, applies the fourth,
  `Henniart.Extension.supercuspidalCorrespondenceHenniartFiveInputs`, the
  sixth, applies the fifth, and
  `Henniart.Extension.supercuspidalCorrespondenceHenniartThreeInputs`, the
  seventh, applies the sixth; see the next four sections.

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

## Published: the six-premise reduction

Worker 4803 (Task 4803) published the fifth theorem, recorded in the shared
planning graph as candidate `5ab85077-a08d-471e-99ea-ef0d26655e22`:

- `Henniart.Extension.supercuspidalCorrespondenceHenniartRankOneInputs`
  (module `Correspondence/HenniartCorrespondenceRankOneInputs`) proves
  `SupercuspidalCorrespondenceStatement.{uK, uW, uV}` from six propositions,
  listed below. It applies `supercuspidalCorrespondenceHenniartSixInputs`
  with two of that theorem's premises discharged:
  - S2, normalized local reciprocity, by the published
    `LocalClassField.commonClosureReciprocityExistence` (module
    `ClassFieldTheory/Local/CommonClosureExistenceProof`; artifact
    `9119eeeb-d405-41b5-bdb8-9997f722b114`, by Worker 125 for Task 4919);
  - S5, Tate's spectral conductor formula, by the published reduction
    `LocalFactor.SpectralConductor.spectralConductorRankOneReduction` (module
    `LocalFactor/SpectralConductorReduction`). For every p-adic field `F`, this
    reduction derives the formula from two premises: refinement invariance
    of presentation conductors and rank-one conductor transport in the
    common closure. Its proof also uses the published
    degree-zero generation `commonClosureDegreeZeroGeneration` and the
    induction identity `conductorFunctional_induce_eq` (module
    `LocalFactor/SpectralConductorInduction`; Serre 1979, VI §2, Prop. 4).

Its six premises are S1, S3, S4, refinement invariance of presentation
conductors (`∀ p K A, Ramification.Padic.FiniteInertiaConductorRefinementStatement K A`;
Serre 1979, IV §3 and VI §2, Prop. 3), rank-one conductor transport in the
common closure and S6, in this order.

## Published: the five-premise entry

Worker 4803 (Task 4803) published the sixth theorem as candidate
`aad00330-42c6-43e6-9a1a-2bebc28da271`; it entered the Library at commit
`cfedefb680f317b0ea5d351023e1c9dd886b2547`:

- `Henniart.Extension.supercuspidalCorrespondenceHenniartFiveInputs` (module
  `Correspondence/HenniartCorrespondenceFiveInputs`) proves
  `SupercuspidalCorrespondenceStatement.{uK, uW, uV}` from five
  propositions, listed in the next two sections. It applies
  `supercuspidalCorrespondenceHenniartRankOneInputs` and supplies refinement
  invariance, that theorem's fourth premise, as
  `fun p _ K A => Ramification.Padic.finiteInertiaConductorRefinement K A`.
- `Ramification.Padic.finiteInertiaConductorRefinement` (module
  `LocalFactor/Ramification/InertiaConductorRefinementProof`) proves
  `FiniteInertiaConductorRefinementStatement F A` for every p-adic field `F`
  and every finite-dimensional complex representation `A` of its local Weil
  group, at independent field and carrier universes. This was the target of
  Task 5737 (`867d5dff-b37c-4c7e-a3e8-c0286f83531b`), which is done. Its
  Markdown explains the proof: the Artin and Swan sums of a presentation
  depend only on the dimensions of the fixed spaces of the upper
  ramification groups, and the published
  `HerbrandBridge.presentationUpperFixedComparison` identifies those fixed
  spaces for any two presentations of the same representation.

## Published: proofs of two premises

Two of the five premises of `supercuspidalCorrespondenceHenniartFiveInputs`
have Library proofs. This section numbers premises by their position in that
theorem.

- Premise 2, `∀ p K eC, LocalFactor.NonabelianSystem.Exists.{uF, uP} K eC`
  (module `LocalFactor/NonabelianSystem`), is proved by
  `LocalFactor.NonabelianSystem.exists_system` (module
  `LocalFactor/NonabelianSystemExistsProof`; Task 4913,
  `2ee1672e-11b3-4c27-8959-d9b1957ab12d`, done). For every p-adic field `F`
  and reciprocity family `e`, at independent field and representation
  universes, it applies the published specialization
  `NonabelianBrauer.exists_of_kernelCompatibilityStatement` (module
  `LocalFactor/NonabelianBrauerSystem`) to the published proof
  `NonabelianBrauer.kernelCompatibilityStatement` of Deligne's Brauer kernel
  compatibility (module `LocalFactor/NonabelianBrauerKernelProof`, Worker 5093,
  Task 5093 `92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, done). That proof applies
  the published `ClassField.Global.RelativeWeilGroup.localTransferReciprocity`
  (module `ClassField/Global/LocalRelativeWeilTransferProof`, Worker 5086).
- Premise 4,
  `∀ p K, LocalFactor.SpectralConductor.CommonClosureRankOneConductorStatement.{uF} K`
  (module `LocalFactor/SpectralConductorRankOneStatement`; Serre 1979, XV §2,
  Thm 1 and Cor. 2–3; VI §2, Prop. 5), is proved by
  `LocalFactor.SpectralConductor.commonClosureRankOneConductor` (module
  `LocalFactor/SpectralConductorRankOneProof`; Task 5815,
  `cbf11cf8-6abd-4db5-a59b-7b47c5b26585`, done; Worker 96 with Workers 4803
  and 4918). The premise says that, at an intermediate field `L` of the common
  closure, the Artin sum of an inertia character of a finite Galois `M/L`
  equals the multiplicative conductor of the character of `L^×` attached by
  the supplied normalized reciprocity family to an agreeing character of
  `W_L`. The proof's Markdown records that it uses no unproved Library
  proposition; in particular it does not assume
  `LocalClassField.FiniteCharacterConductorTheorems` (Task 5738) or
  `Ramification.Padic.FiniteGaloisConductorInflationStatement` (Task 5739).
  Its Galois-side input is Worker 4918's module
  `LocalFactor/Ramification/RankOneArtinSum`.

## Published: the three-premise entry

Worker 4803 (Task 4803) published the seventh theorem; it is in the Library
at commit `2e46b9ca`:

- `Henniart.Extension.supercuspidalCorrespondenceHenniartThreeInputs` (module
  `Correspondence/HenniartCorrespondenceThreeInputs`) proves
  `Henniart.Extension.SupercuspidalCorrespondenceHenniartThreeInputsStatement.{uK, uW, uV}`.
  That statement says that candidate existence
  (`CandidateExistenceStatement.{uK, uW, uV, uW, uK}`), numerical
  surjectivity (`NumericalSurjectivityStatement.{uK, uW, uV}`) and the JPSS
  conductor exponent (`Conductor.ConductorExponentStatement.{uK, uV}`)
  together imply `SupercuspidalCorrespondenceStatement.{uK, uW, uV}`. These
  are premises 1, 3 and 5 of `supercuspidalCorrespondenceHenniartFiveInputs`,
  in the same order and at the same universe levels. The proof applies that
  theorem and supplies premise 2 as
  `fun p _ K eC => NonabelianSystem.exists_system K eC` and premise 4 as
  `SpectralConductor.commonClosureRankOneConductor`.

## The three open premises

The table lists the three premises of
`supercuspidalCorrespondenceHenniartThreeInputs`, which have no Library proof
at commit `f676fad7`. They are numbered by their position in that theorem;
the third column gives their position among the premises of
`supercuspidalCorrespondenceHenniartFiveInputs`, which the eighth version
used. Universes are those of the full correspondence (`uK = uF`, `uW = uP`,
`uV = uA`).

The owners and states below are TaskHub task records as inspected on
14 November 2026; they are not part of the Library commit. A candidate that is
staged or under review is not a proof until it is accepted and published.

| # | Premise (universes of the full correspondence) | Five-premise position | Module | Owner and state on 14 November 2026 |
| --- | --- | --- | --- | --- |
| 1 | `Henniart.CandidateExistenceStatement.{uF, uP, uA, uP, uF}` (Henniart 2000, Thm 3.1 with §§3.7–3.8) | 1 | `Correspondence/HenniartStableMapStatement` | Task 5583 `54bed1a5-c9db-4be3-b59b-e4eb4abb89b8`, waiting; executor Worker 5732. See below. |
| 2 | `Henniart.NumericalSurjectivityStatement.{uF, uP, uA}` (Henniart 1988, Thm 1.2) | 3 | `Correspondence/HenniartNumericalStatement` | Task 5584 `35ad7726-c0bc-499a-ba29-69e4bc6e3c2a`, waiting; executor Worker 5733. It needs Tasks 6305 and 5032; Task 6304, which it also waited on, is done. It has no proof candidate; its route-study note is published. See below. |
| 3 | `Conductor.ConductorExponentStatement.{uF, uA}` (Jacquet–Piatetski-Shapiro–Shalika 1981, Thm (5.1)) | 5 | `Representation/Conductor/EssentialStatement` | Task 5032 `7b8711bf-90dc-40ae-923e-5bfecc3550b6`, waiting; executor Worker 5032. The second executor, Worker 5731, published proof Tasks 5949 (`6cf78338-9b48-4893-a844-ba5c1273825e`) and 5950 (`85efb316-26c1-4be2-b19f-b30dbd78e2ee`) on unramified principal series and then left the task. Both are done; see below. The premise is the second conjunct of that task's target `Conductor.EssentialConductorStatement`. |

Premise 1. Task 3657 published the proposition
`Henniart.CandidateExistenceReductionStatement.{uK, uW, uP, uE, uQ}` (module
`Correspondence/HenniartCandidateExistenceReductionStatement`). Task 6289
(`207f459d-c3ed-4e90-b4e8-c71e0bba6101`, done) proved it:
`Henniart.candidateExistenceReduction` (module
`Correspondence/HenniartCandidateExistenceReductionProof`; Lean proof by
Worker 390, candidate `79c92440`). The statement says that five global inputs
together imply `CandidateExistenceStatement.{uK, uW, 0, uE, uQ}`, that is,
candidate existence with the automorphic-lattice universe (the third
universe argument) equal to `0` and the other four universes arbitrary. The
inputs, at the universes of the statement, are:

1. `Global.Harris.Proposition48Statement.{uK, 0, 0, 0, uP}` (Harris 1998,
   Prop. 4.8);
2. `ClassField.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP}`
   (Henniart 2000, Thm 2.4);
3. `ClassFieldTheory.Local.LocalRelativeClassFormationStatement.{0}`;
4. `Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement.{0, uW, uP}`
   (Henniart 2000, Lemme 2.8);
5. `Global.PoleComparison.HenniartCompositeMapStatement.{0, uK, uW, uP, uE}`
   (Henniart 2000, §3.8).

The universe `0` comes from the globalization, which produces number fields
in `Type`. The route needs candidate existence with the automorphic universe
`uA` arbitrary. The statement's Markdown leaves the passage between these
universes to Task 5583. The operator decided on 13 November 2026 that Task
5583 keeps its unconditional target unchanged. Its executor waits on the
tasks below, which own the inputs. A search of the Lean sources at commit
`f676fad7` found a proof of input 3 and of none of the others. The states are
TaskHub records of 14 November 2026.

- The reduction itself: proved. Task 6289
  (`207f459d-c3ed-4e90-b4e8-c71e0bba6101`, Worker 390, reusing Worker 3657's
  draft) published candidate `79c92440-93ac-4787-921c-1ac6edd613cf` (review
  task `edf18bca-ab64-44a7-8b77-11ef151d13fd`, Reviewer 2712) in Library
  `457e31a2` on 14 November 2026. It contains
  `theorem Henniart.candidateExistenceReduction :
  CandidateExistenceReductionStatement.{uK, uW, uP, uE, uQ}`. The same
  candidate removed the duplicate declaration
  `Automorphic.OperatorRealization.evaluate_toContinuous_smul` that had blocked
  the proof. That theorem is now declared once, in the new module
  `Automorphic/OperatorRealizationEvaluation`. The reduction is conditional:
  its five inputs are listed below, and only input 3 has a Library proof.
- Input 1, Harris 1998, Prop. 4.8: no Library proof.
  - Task 6702 (`0aa2189a-e878-4144-9d41-b76799d87cfc`, `lean.proof@1`,
    ready, no executor and no candidate) owns the proof of the unchanged
    `Global.Harris.Proposition48Statement` at `.{uF, 0, 0, 0, uV}` for
    arbitrary `uF` and `uV`; `candidateExistenceReduction` uses it at
    `.{uK, 0, 0, 0, uP}`. Its contract asks for the final assembly from the
    reduction statement `Global.Harris.Proposition48ReductionStatement` and
    the proofs of that statement's inputs. A conditional theorem that leaves
    any of these inputs as hypotheses does not discharge it.
  - The reduction statement is now in the Library (module
    `Global/Arithmetic/HarrisProposition48ReductionStatement`). It says that
    the conjunction of fourteen named propositions implies
    `Proposition48Statement.{uF, 0, 0, 0, uV}`. It has no proof, and a
    TaskHub search found no proof task for it. The table after this list
    gives its fourteen inputs and their owners.
  - The planning Task 6413 (`bca10e59-d4e2-40a4-be9b-5d70eaa1acd2`,
    `lean.peer@1`; ready, executors Workers 514 and 619), published by
    Worker 0, stated the reduction and its inputs. It proves nothing itself.
    Requirement 5 of its contract asks it to publish a focused proof task
    for the reduction statement and, for every input without a proof or a
    proof task, a proof task or a statement and planning task. Worker 514
    published Task 6702 and the planning Tasks 6698 and 6699 under it, and
    Workers 514 and 619 published the proof Tasks 6845 and 6846.
  - Task 5134 (`1b87b965-a232-4c02-a51f-e287f630c549`) is a consumer: its
    target is that Harris's Prop. 4.8 implies
    `HenniartGlobalizationStatement`.
- Input 2, Henniart 2000, Thm 2.4: Task 4933
  (`65c9a94c-af88-4876-baa4-43d78ccd5531`, `lean.proof@1`, waiting; executor
  Worker 4933), Henniart's local induction from unitary supercuspidals for
  associated pairs. One candidate of the task, `d5ad9940`, was rejected
  because it proved the statement only under three added hypotheses:
  `AssociatedGammaStatement`, the exhaustion of unitary generic
  representations, and `NonabelianSystem.Exists`. The task requires a proof
  without added hypotheses.
- Input 3, local relative class formation: proved. Task 6411
  (`03546f9b-94c7-4620-b762-48c39652bbff`, done) published
  `ClassFieldTheory.Local.localRelativeClassFormation` (module
  `ClassFieldTheory/Local/LocalRelativeClassFormationProof`; Lean proof by
  Worker 513, candidate `7c056ded`). It proves
  `LocalRelativeClassFormationStatement.{u}` at every universe `u`. The proof
  keeps the invariant family of the published
  `ClassFieldTheory.Local.localAbsoluteCorestrictionCompatibleClassFormation`
  and drops six of its fifteen conjuncts.
- Input 4, Henniart 2000, Lemme 2.8: Task 6017
  (`0f17fd08-105e-4659-b949-42f622d60eaa`, waiting; executor Worker 406) is
  to prove `RelativeCertifiedPoleComparisonsStatement`.
- Input 5, Henniart 2000, §3.8: Task 5231
  (`9e23a040-16d7-4a7a-bd9b-35a08938d3c4`, waiting; executor Worker 5093) is
  to prove `HenniartCompositeMapStatement` by combining four published
  propositions. Three of them have Library proofs at commit `f676fad7`:
  `Global.PoleComparison.relativeIsometryOperation` proves
  `RelativeIsometryOperationStatement` (module
  `Global/Factors/RelativeIsometryOperationProof`);
  `Global.PoleComparison.henniartCompositeOperation` proves
  `HenniartCompositeOperationStatement` (module
  `Global/Factors/HenniartCompositeOperationProof`; Task 5228
  `3562e8a2-a9cf-412d-959f-04f43884373c`, done); and
  `Global.PoleComparison.henniartCompositeFactor` proves
  `HenniartCompositeFactorStatement` (module
  `Global/Factors/HenniartCompositeFactorProof`; Task 5230
  `2a08796a-fc06-4ed1-ab5a-7751da0b394b`, done). The fourth,
  `Global.PoleComparison.RelativeIsometryFactorStatement` (compatibility of
  the generated isometry with determinants and with pair L- and ε-factors),
  has no Library proof. Task 5191 (`c7b60e52-3b3a-45a4-a9f2-595674545493`,
  waiting; executors Workers 5159 and 5121) is to prove it.
- Task 3657 (`34b81620-20d7-4059-9b08-6bedd1c1c029`, ready; executor
  Worker 3657) is the program task for Henniart's global construction (Henniart
  2000, §3). The candidate-existence reduction statement, the statements of
  Lemme 2.8 and §3.8, and the proof Tasks 5191, 5231, 6017 and 6289 were
  published from it.

The fourteen inputs of `Global.Harris.Proposition48ReductionStatement`, in
their Lean order, follow. The universes are those at which the reduction
uses them. Modules are relative to `Langlands/`. The names are in the
namespaces `Langlands.Global.Harris` (rows 1–6 and 10),
`Langlands.GaloisRepresentation` (rows 7 and 8) and
`Langlands.Automorphic.Unramified` (rows 9 and 11–14). The descriptions
paraphrase the docstrings and Markdown of the statements. None of the
fourteen has a Library proof at commit `f676fad7`. The owners are TaskHub
records of 14 November 2026. "No task found" means that TaskHub searches
for the statement's name and topic found no proof or planning task for it.
The three proof tasks named below require their targets at arbitrary
independent universes, which covers the universes of this table.

| # | Input statement (universes in the reduction) | Module | Content | Owner on 14 November 2026 |
| --- | --- | --- | --- | --- |
| 1 | `Proposition48AuxiliaryRankOneStatement.{uF, uV}` | `Global/Arithmetic/HarrisProposition48AuxiliaryInputStatement` | Base case `[E' : E] = 1` of the one-place induction: realization by a Hecke character, using only the auxiliary place | No task found |
| 2 | `Proposition48AuxiliaryParityNormalizationStatement.{uF}` | same module | Correction of the inherited infinity parity by a conjugate-inverse Hecke character of the base field | No task found |
| 3 | `Proposition48AuxiliaryParityUntwistStatement.{uF, uV}` | same module | Undoing that correction on a supplied solution of the corrected problem | No task found |
| 4 | `Proposition48MackeyStepStatement.{uF}` | `Global/Arithmetic/HarrisProposition48MackeyStepStatement` | One prime cyclic Mackey step with all its children, of smaller normal-closure degree and inherited parity | No task found |
| 5 | `Proposition48PrimeBranchStatement.{uF, uV}` | `Global/Arithmetic/HarrisProposition48PrimeBranchStatement` | Assembly of the Mackey constituents of a prime orbit | No task found |
| 6 | `Proposition48SingletonBranchStatement.{uF, uV}` | `Global/Arithmetic/HarrisProposition48SingletonBranchStatement` | Cyclic descent of a singleton Mackey constituent (Harris 1998, Lemma 1.6) | No task found |
| 7 | `Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV}` | `Galois/Harris1998ExistenceStatement` | Cuspidal case of Harris 1998, Thm 1.2 | Planning Task 6698 (`cd19dd55-136e-42e9-b062-5a23b2c7a6b2`, `lean.peer@1`, ready, no executor) |
| 8 | `HarrisSupercuspidalLocalComparisonStatement.{0, 0, uV, uV}` | `Galois/HarrisSupercuspidalLocalComparisonStatement` | Equal supercuspidal components at a split place give isomorphic local Galois restrictions (derived from Harris 1999, Thm 5.9(ii)) | Proof Task 6846 (`2aa19068-4bd1-4522-8eb4-6d6a159e5e77`, `lean.proof@1`, ready, no executor) |
| 9 | `CuspidalSpectralRigidityStatement.{0, uV}` | `Automorphic/Unramified/CuspidalSpectralRigidityStatement` | Mixed-rank cuspidal spectral rigidity | Proof Task 6446 (`c4f0be57-1a49-4a42-b813-4354e297ab3f`, `lean.proof@1`, ready, no executor) |
| 10 | `Proposition48IsobaricInvarianceStatement.{uV}` | `Global/Arithmetic/HarrisProposition48IsobaricInvarianceStatement` | Galois invariance of the isobaric multiset from equal Euler systems | No task found |
| 11 | `CyclicRegularInductionStatement.{0, 0, uV, uV}` | `Automorphic/Unramified/CyclicTransferStatement` | Arthur–Clozel, Lemma III.6.4 with Thm III.6.2, in weak-induction form | Planning Task 6699 (`ca76241a-30bc-46d4-a0b9-5f6c284363a5`, `lean.peer@1`, ready, no executor) |
| 12 | `CyclicRegularOrbitLiftStatement.{0, 0, uV, uV}` | `Automorphic/Unramified/IsobaricCyclicTransferStatement` | Arthur–Clozel, Lemma III.6.4, in base-change form | Planning Task 6699 |
| 13 | `CyclicStableDescentStatement.{0, 0, uV, uV}` | `Automorphic/Unramified/CyclicTransferStatement` | Arthur–Clozel, Lemma III.6.3 | Planning Task 6699 |
| 14 | `CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV}` | `Automorphic/Unramified/CyclicWeakInductionSupercuspidalStatement` | Supercuspidality at a place of a cyclic weak induction (derived from Henniart–Herb 1995, Prop. 5.5) | Proof Task 6845 (`3064d640-8ebf-4ac1-807c-a48f48d653c4`, `lean.proof@1`, ready, no executor) |

So the reduction itself and inputs 1–6 and 10 have no proof task. Requirement
5 of Task 6413's contract assigns their proof tasks to that task. The
earlier published statement `Global.Harris.Proposition48RankOneStatement`
(module `Global/Arithmetic/HarrisProposition48RankOneStatement`; every valid
problem with `[E' : E] = 1` has a solution) is not one of the fourteen
inputs. Input 1 is the corresponding base case under the one-place
hypotheses `IsAuxiliaryValid` of the internal induction, which impose no
condition at the primary place. The structure
`Global.Harris.Proposition48Problem` (module
`Global/Arithmetic/HarrisProposition48InductionData`) bundles the data of one
instance of `Proposition48Statement`, with the number fields in `Type`; the
statement's Markdown describes how the induction uses it. The shared planning
graph's node `proof.harris-global-input` records the Harris-branch
dependencies.

The transport of supercuspidal unitary lattices between carrier universes,
which the globalization in universe 0 makes necessary, is a helper in
Task 5583's draft. The second theorem of the composite below avoids this
transport: it fixes the representation universe of the full correspondence
at `0`.

Premise 2. Task 5891 (`e69d09d4-6da8-4810-886b-664574e533f8`, done) proved
the counting reduction of Henniart 1988, §2.8, in orbit form:
`Henniart.numericalOrbitReduction` (module
`Correspondence/HenniartNumericalReductionProof`; Lean proof by Worker 5733,
checked by Worker 5428) proves `Henniart.NumericalOrbitReductionStatement`. That
statement says that `NumericalSurjectivityStatement` follows from two
hypotheses: `NumericalOrbitCountStatement` (for every p-adic field, rank and
conductor, the unramified-twist orbit strata on the Weil and supercuspidal
sides are finite and have equal cardinality), and finiteness of the conductor
`Numerical.conductor K π` of every supercuspidal class `π`. A search of the
Lean sources at commit `f676fad7` found no proof of either hypothesis. The
operator decided on 13 November 2026 that Task 5584 stays open and that its
executor does not prove conductor finiteness of supercuspidal classes: that is
owned through Task 5585 (`5da7d945-39ed-4dcb-ace6-030fa18e4f24`,
Bernstein–Zelevinsky 1976, Cor. 4.15) and Task 5032. Task 5585 is now done:
`Henniart.supercuspidalCompactOpenFiniteness` (module
`Correspondence/SupercuspidalCompactOpenFinitenessProof`; Lean proof by Workers
254 and 261, candidate `3a9c910a-ed76-48b9-97f7-2b4263ec94bf`) proves
`Henniart.SupercuspidalCompactOpenFinitenessStatement`. That statement says
that only finitely many supercuspidal classes have a given central character
and a nonzero vector fixed by a given compact open subgroup. It does not say
that every supercuspidal class has a nonzero vector fixed by one of the
last-row congruence subgroups that define `Numerical.conductor`, which is what
conductor finiteness asserts. The search above found no proof of conductor
finiteness, and Task 5032 remains its other owner. The
executor of Task 5584 wrote a route-study note,
[Henniart's numerical correspondence: route study for the orbit counts](numerical-count-route-study.md),
which compares Henniart's 1988 route to the orbit counts with a route through
explicit counts.

`NumericalOrbitCountStatement` has three conjuncts for each p-adic field `K`,
rank `k + 1` and conductor `a`: the Weil-side orbit stratum is finite, the
supercuspidal orbit stratum `Numerical.supercuspidalOrbitStratum K k a` is
finite, and the two have the same `Set.ncard`. On 13 November 2026 the operator
approved the first unit proposed in the route-study note: the finiteness of the
supercuspidal orbit strata, as a statement task followed by a proof task
(operator message `61fe2f523b935694829f4bc257c86858`, to the executor of Task
5584). The executor of Task 5584 published both:

- Task 6304 (`4ac43c6c-0bda-415d-b426-54cc423c10b9`, `lean.statement@1`,
  done) published `Henniart.SupercuspidalOrbitStratumFinitenessStatement.{uK, uV}`
  (module `Correspondence/HenniartOrbitStratumFinitenessStatement`; Worker
  408, candidate `15a445fd`). It says that for every p-adic field `K`, rank
  `k + 1` and conductor `a`, the set
  `Numerical.supercuspidalOrbitStratum.{uK, uV} K k a` is finite: the second
  conjunct above.
- Task 6305 (`44507d44-e3fd-4b88-a5cf-8efd43844948`, `lean.proof@1`, ready,
  no executor yet) is to prove it in a module
  `Correspondence/HenniartOrbitStratumFinitenessProof`.

A Lean draft of the proof is in Task 5584's shared draft (revision 2). It
reduces to the published
`Henniart.CompactOpenFiniteness.centralLevelStratum_finite` (Bernstein–Zelevinsky
1976, Cor. 4.15, for p-adic fields). The draft is not a candidate, and the
Library at commit `f676fad7` has no proof module. The operator did not approve
the second unit proposed in the note, which would derive the counts from a
bijective numerical injection in every rank. The operator judged it circular
for this route: every known source of such an injection is a local Langlands
correspondence whose proof uses the numerical theorem. TaskHub searches on
13 and 14 November 2026 found no task for the Weil-side finiteness or the
equality of the counts. The operator will decide later on
a program for them, such as Henniart's 1988 route (Route A of the route-study
note).

Premise 3. `Conductor.ConductorExponentStatement` has no Library proof at
commit `f676fad7`. The published `Conductor.conductorExponentStatement_of`
(module `Representation/Conductor/EssentialConductorReduction`) derives it
from five hypotheses. Two of them are proved:
`Whittaker.MirabolicRestrictionInjectivityStatement`, by
`Whittaker.mirabolicRestrictionInjectivity` (module
`Representation/Whittaker/MirabolicRestrictionInjectivityProof`), and
`Conductor.TrivialCharacterEpsilonStatement`, by
`Conductor.trivialCharacterEpsilon` (module
`Representation/Conductor/TrivialCharacterEpsilonProof`). A search of the
Lean sources found no unconditional proof of the other three:
`Conductor.EssentialVectorExistence`, `Conductor.EssentialDualComparisonStatement`
and `Conductor.ConductorMinimalityStatement`. Published theorems derive the
last two from spherical functional-equation statements and mirabolic
injectivity. Task 5032 owns the premise; this note does not record how its
executor plans to prove these three.

Since the fourteenth version, the two proof tasks that Worker 5731 published
from Task 5032 are done. Their targets are the two conjuncts of
`Conductor.OrderedUnramifiedWhittakerStatement` (module
`Representation/Conductor/OrderedUnramifiedWhittakerStatement`), the two
assertions about unramified principal series that the statement's
docstring attributes to Jacquet's corrected essential-vector argument
(Jacquet 2012, Lemmas 1 and 2). `Conductor.orderedUnramifiedSphericalCyclicity`
(module `Representation/Conductor/OrderedUnramifiedSphericalCyclicity`;
Worker 392, Task 5949) proves `OrderedUnramifiedSphericalCyclicityStatement`:
the normalized spherical section generates the whole principal series when
the norms of the parameters are nondecreasing.
`Conductor.orderedUnramifiedWhittakerRealization` (module
`Representation/Conductor/OrderedUnramifiedWhittakerProof`; Task 5950)
proves `OrderedUnramifiedWhittakerRealizationStatement`: there is a nonzero
inverse-character functional with injective coefficient map that sends the
spherical section to the explicit spherical Whittaker function. Both
theorems hold for every nonarchimedean local field, at every field universe.

## Tasks that left the route

The seventh version listed premises 2 and 4 of
`supercuspidalCorrespondenceHenniartFiveInputs`, owned by Tasks 4913 and 5815,
as open. Both are now proved, as described above, and both tasks
are done. The seventh version also named an alternative route to premise 4,
through finite abelian conductor transport
(`LocalClassField.FiniteCharacterConductorTheorems`, Task 5738,
`cbe92f65-9440-440c-93e1-9817d4aa300f`) and inflation of conductors
(`Ramification.Padic.FiniteGaloisConductorInflationStatement`, Task 5739,
`1e35eaa4-0bf9-4e1f-b16f-cc202c9d3b3a`). The published proof does not use these
statements, so the route no longer needs Tasks 5738 and 5739. These statements
remain the targets of their tasks.

The sixth version listed refinement invariance of presentation conductors,
`∀ p K A, Ramification.Padic.FiniteInertiaConductorRefinementStatement.{uF, max uF uP} K A`,
as its fourth premise, owned by Task 5737. The published
`finiteInertiaConductorRefinement` proves it, and Task 5737 is done.

The fifth version of this note listed `∀ p K,
ConductorExponent.SpectralConductorStatement.{uF, uP} K` as its fifth premise,
owned by Task 5626 (`24b84ed8-5c32-460b-b50b-30a1c08fb408`). The published
`spectralConductorRankOneReduction` derives it from refinement invariance
and premise 4 of the five-premise theorem, both now proved, so the route no
longer needs Task 5626. The
same holds for the conductor laws that Task 5626's suggested route needed: Task 5651
(`62ccf2f8-9d7b-4b62-bb2f-231ce16e1916`, additivity in short exact sequences)
and Task 5661 (`32abafa4-2d05-4dab-9a1f-d0b58dcdc86e`, conductors of induced
representations). Of the conductor clauses of the target of Task 5676
(`b1cfcfb8-bef5-4a1f-ad85-7c0c1c45d5bd`),
`Ramification.Padic.InertiaSurjectivityPresentationAndConductorIndependenceStatement` (module
`LocalFactor/Ramification/InertiaPresentationStatement`), the route uses only
clause 6, refinement invariance, which was Task 5737's target on its own and is
proved by `finiteInertiaConductorRefinement`. These statements remain the
targets of their tasks; this note does not record those tasks' current state
or the status of the other clauses.

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
field, including fields of positive characteristic. Task 5585 has since
proved it in that generality (`Henniart.supercuspidalCompactOpenFiniteness`, see
premise 2 above) and is done.

## The composite

The module below compiles at commit
`f676fad71e1679d672d3e20560dc814d4e1f8ffd` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with 0 errors and 0 warnings. The
check compiled the block verbatim as a private draft module in the Lean
service, together with a second draft module that imports it and runs
`#print axioms` on both theorems. The service's declaration inspection was
run once for each theorem; each lists only the axioms `propext`,
`Classical.choice` and `Quot.sound`. The diagnostics are the private records
`3dd3953b-d185-4a3c-ad07-e9dda611dc7d` (first theorem) and
`847876cd-5b29-4206-91c1-91916a01506f` (second theorem). To reproduce them,
save the block as a draft module and compile it with `lean_check`, naming
each theorem as the declaration to inspect. The module is a development
check, not a published proof.

The first theorem, `fullCorrespondence_of_henniartThreeInputs`, applies two
published theorems: `fullCorrespondenceStatement_of_supercuspidalCorrespondence`
and `supercuspidalCorrespondenceHenniartThreeInputs`. Its hypotheses are the
three open premises, in the order of the table. The eighth to fourteenth
versions had the same theorem. The eighth version's proof applied
`supercuspidalCorrespondenceHenniartFiveInputs` with
`NonabelianSystem.exists_system` and
`SpectralConductor.commonClosureRankOneConductor` directly, before the
three-premise theorem was published. The seventh version's composite,
`fullCorrespondence_of_henniartFiveInputs`, also assumed premises 2 and 4 of the
five-premise theorem. The sixth version's composite,
`fullCorrespondence_of_henniartRankOneInputs`, assumed refinement invariance as
well.

The second theorem, `fullCorrespondence_zero_of_henniartGlobalInputs`, was
added in the fourteenth version. Its conclusion is `FullCorrespondenceStatement.{uF, uP, 0}`:
the full correspondence with the representation universe `uA` equal to `0`.
It applies the first theorem at `uA = 0`. It obtains premise 1 at these
universes, `CandidateExistenceStatement.{uF, uP, 0, uP, uF}`, from
`candidateExistenceReduction.{uF, uP, uS, uP, uF}`. The published
`localRelativeClassFormation.{0}` supplies that reduction's third input. The
other four inputs are hypotheses, at the universes that the reduction
requires: Harris's Prop. 4.8, Henniart's Thm 2.4, Lemme 2.8 and §3.8.
The universe `uS` is the reduction's third universe parameter; it occurs only
in these four hypotheses. Premises 2 and 3 are hypotheses at `uA = 0`. The
theorem does not prove the target at an arbitrary universe `uA`; Task 5583
owns that passage (see premise 1 above).

```lean
import Langlands.Correspondence.FullCorrespondenceReduction
import Langlands.Correspondence.HenniartCorrespondenceThreeInputs
import Langlands.Correspondence.HenniartCandidateExistenceReductionProof
import Langlands.ClassFieldTheory.Local.LocalRelativeClassFormationProof

namespace Langlands.Correspondence

universe uF uP uA uS

open Langlands.Henniart LocalFactor in
/-- The full correspondence from the three premises of the published
`supercuspidalCorrespondenceHenniartThreeInputs` that the Library does not prove:
candidate existence, numerical surjectivity and the JPSS conductor exponent. -/
theorem fullCorrespondence_of_henniartThreeInputs
    (hCE : CandidateExistenceStatement.{uF, uP, uA, uP, uF})
    (hnum : NumericalSurjectivityStatement.{uF, uP, uA})
    (hJPSS : Conductor.ConductorExponentStatement.{uF, uA}) :
    FullCorrespondenceStatement.{uF, uP, uA} :=
  fullCorrespondenceStatement_of_supercuspidalCorrespondence
    (Extension.supercuspidalCorrespondenceHenniartThreeInputs.{uF, uP, uA} hCE hnum hJPSS)

open Langlands.Henniart LocalFactor in
/-- Universe-`0` variant: with automorphic carrier universe `0`, candidate existence is
replaced by four of the five inputs of the proved `candidateExistenceReduction`.
The fifth input, local relative class formation, is the published theorem
`ClassFieldTheory.Local.localRelativeClassFormation` (Task 6411). -/
theorem fullCorrespondence_zero_of_henniartGlobalInputs
    (hHarris : Global.Harris.Proposition48Statement.{uF, 0, 0, 0, uS})
    (hasi : ClassField.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionStatement.{0, uP, uS, uS})
    (hpole : Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement.{0, uP, uS})
    (hcomp : Global.PoleComparison.HenniartCompositeMapStatement.{0, uF, uP, uS, uP})
    (hnum : NumericalSurjectivityStatement.{uF, uP, 0})
    (hJPSS : Conductor.ConductorExponentStatement.{uF, 0}) :
    FullCorrespondenceStatement.{uF, uP, 0} :=
  fullCorrespondence_of_henniartThreeInputs.{uF, uP, 0}
    (candidateExistenceReduction.{uF, uP, uS, uP, uF} hHarris hasi
      ClassFieldTheory.Local.localRelativeClassFormation.{0} hpole hcomp)
    hnum hJPSS

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
