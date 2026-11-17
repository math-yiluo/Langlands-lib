# Local Langlands for GL_n: published reductions and the remaining premises

Author: Worker 0, for Task 0 (`69dd20b3-6a77-44aa-b779-32391843c8dd`). First
version 10 November 2026, second version 11 November 2026, third, fourth and
fifth versions 12 November 2026, sixth to thirteenth versions 13 November
2026, fourteenth to sixteenth versions 14 November 2026, seventeenth to
nineteenth versions 15 November 2026, twentieth version 17 November 2026.
This twenty-first version, of 17 November 2026, was checked against Library
commit `fcb85a7ef43356fec01e6ccf1605f08568c08cb0`. Between commits
`9e39a73d21bd6ed6fac00b01cc5e01c0db5d105b` and `fcb85a7e` the Library
changed no Lean file; it changed notes, among them the twentieth version of
this note, and the wiki index. The twentieth version was checked against
commit `9e39a73d`. Its text was first checked
against commit `314cfd1a0275806b9ff4281f3d3e51a05e9a6cb5`, and the Lean
facts that it states at commit `314cfd1a` also hold at commit `9e39a73d`:
between the two commits the Library added 131 Lean modules and changed
seven Lean files, none of which this note names, and none of the added
modules mentions a proposition that this note names. The nineteenth version was checked
against commit `72480b70c88adff84a438bd7029d64ee3977469c`, the eighteenth
against commit `fab9caeae532b7a65e67e702bcab72d3194371ae`, and the
seventeenth against commit `5764b3a9`, which has the same Lean sources as
commit `544dba099880b57da5fdc3cbc715c01cf2579eb2`. Between commits
`5764b3a9` and `72480b70`, the Library added Lean modules and changed seven
Lean files that this note does not name. The added modules that bear on this
note are the two statements on the chain of premise 3 below,
`Conductor.ConductorMinimalityProof` (Task 5549), the proof of Task 6305
under premise 2 and the proof of Task 7044 under premise 3. Between commits
`72480b70` and `314cfd1a`, the Library added 1584 Lean modules and changed
nine Lean files, all under `BruhatTits/`, `Geometry/Building/` and
`GroupScheme/`, that this note does not name. The added modules that bear on
this note are the proof of Task 7045 (see "Published: the two-premise entry"
below), the totally complex statements and reductions under premise 1, and
the proofs of Tadić's exhaustion of the unitary dual and of the exhaustion of
unitary generic representations (input 2 of premise 1). A search of the Lean
files added since commit `5764b3a9` for the names of the open propositions
of this note found no other proof of them. So the Lean facts that this note
states at commit `544dba09` also hold at commit `314cfd1a`, except where the
text says otherwise.

This note records how the published Library reduces the full local Langlands
correspondence for GL_n to two propositions, candidate existence and
numerical surjectivity, and names the task that owns each of them. The
newest published reduction of the supercuspidal correspondence,
`Henniart.Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor`
(Task 7045), has three premises: these two and the supercuspidal p-adic
variant of the conductor exponent theorem of Jacquet–Piatetski-Shapiro–Shalika
(JPSS). The variant is proved, by
`Conductor.supercuspidalPadicConductorExponent` (Task 7044). The first
theorem of the composite Lean module below combines these two theorems with
the published passage from the supercuspidal to the full correspondence. It
proves the full correspondence from candidate existence and numerical
surjectivity alone. The module has been compiled as a development check but
is not published. Each of the two open propositions still needs an accepted
`lean.proof@1` candidate. The general JPSS conductor exponent statement, the
third premise of the earlier three-premise theorem, is no longer needed on
the route; see "Tasks that left the route".

The Library also proves a reduction of the first premise, candidate
existence, to five global inputs: `Henniart.candidateExistenceReduction`. It
gives candidate existence only with the automorphic-lattice universe equal to
`0`. One of the five inputs, local relative class formation, is proved. So
the composite module has a second theorem. It proves the full correspondence
with representation universe `0` from the four other global inputs and
premise 2. Premise 1 below names the tasks that own those four inputs; all
four have proof tasks. The global inputs are now pursued over totally complex
number fields. The third theorem of the composite does the same as the second
with the totally complex forms of three of the global inputs. It assumes in
addition the published totally complex reduction statement, which has a proof
task but no proof yet.

For the first of these inputs, Harris's Prop. 4.8, the Library has a
reduction statement, `Global.Harris.Proposition48ReductionStatement`: fourteen
named propositions together imply it. Neither the reduction nor any of its
fourteen inputs has a Library proof. Since the nineteenth version, the
planning task for them has published proof or planning tasks for the
reduction and for every input that had none. On 16 November 2026 the
operator published a task that restates Prop. 4.8 under an exact-stabilizer
condition; the present formulation stays open as the fallback. See premise 1
below.

On 16 November 2026 the operator also decided the program for premise 2 and
for the large external inputs of the route (message
`681bfebbe78e534fb445d97c189108c7` to Worker 0). The decisions draw on two
operator notes, registered as literature: `operator-numerical-llc-route-2026-11-16`
(the numerical step) and `operator-external-inputs-plan-2026-11-16` (the
external inputs). This note records the decisions under premises 1 and 2
below and in the section "Operator decisions of 16 November 2026". On 17
November 2026 the executor of premise 2 published the statement tasks and
proof tasks of that program. They include a conditional assembly with five
premises; four of them have proof tasks or proof programs, and the fifth,
input (I4), has none (premise 2 below). For
statement meanings and sources see
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
- `Henniart.Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor`,
  the eighth theorem, by Worker 619 for Task 7045, adapts the route of the
  fourth to seventh theorems to the supercuspidal p-adic conductor variant;
  see "Published: the two-premise entry".

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

## Published: the two-premise entry

Worker 619 published the eighth theorem for Task 7045
(`91b1a919-c763-40e4-b0e7-3ee049060243`, `lean.proof@1`, completed), as
candidate `924fdb59`, crediting a bridge by Worker 0; it is in the Library
since commit `a98af0ff`:

- `Henniart.Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor`
  (module `Correspondence/HenniartSupercuspidalConductorReductionProof`)
  proves
  `Henniart.Extension.SupercuspidalCorrespondenceHenniartSupercuspidalConductorStatement.{uK, uW, uV}`
  at independent universes. That statement, published by Worker 0 under Task
  0, says that candidate existence
  (`CandidateExistenceStatement.{uK, uW, uV, uW, uK}`), numerical
  surjectivity (`NumericalSurjectivityStatement.{uK, uW, uV}`) and the
  supercuspidal p-adic conductor variant
  (`Conductor.SupercuspidalPadicConductorExponentStatement.{uK, uV}`)
  together imply `SupercuspidalCorrespondenceStatement.{uK, uW, uV}`. It is
  the three-premise statement above with its third premise replaced by the
  variant.
- The proof does not apply the three-premise theorem. It applies
  `supercuspidalCorrespondenceHenniartInduction` to candidate existence, to a
  new surjectivity-step reduction (module
  `Correspondence/HenniartSupercuspidalConductorSurjectivity`), to a new
  finiteness result for candidate sets (module
  `Correspondence/HenniartSupercuspidalConductorFiniteness`), both of which
  use only the variant, and to the published proofs of normalized local
  reciprocity and of the existence of local constants. The other published
  inputs are those of the six- to three-premise theorems: Tate's spectral
  conductor formula from `spectralConductorRankOneReduction` with
  `finiteInertiaConductorRefinement` and `commonClosureRankOneConductor`, and
  the pair epsilon exponent statement from `equalRankEpsilonCharacterChange`
  and `pairEpsilonExponentReduction`. The finiteness module uses
  `Conductor.genericConductor_isNewvectorConductor_of_supercuspidalPadic`
  (module `Representation/Conductor/SupercuspidalPadicGenericConductor`),
  which derives from the variant, for a supercuspidal representation, what
  `genericConductor_isNewvectorConductor_of_conductorExponentStatement`
  derives from the general premise (see "Use of the premise in the route"
  under premise 3). The modules' Markdown describes these adaptations.

The variant itself is proved by
`Conductor.supercuspidalPadicConductorExponent` (Task 7044, Worker 388); see
premise 3 below. So the supercuspidal correspondence, and with it the full
correspondence, follows from candidate existence and numerical surjectivity
alone. The first theorem of the composite below checks this in Lean.

## The two open premises

The table lists the two premises of
`supercuspidalCorrespondenceHenniartSupercuspidalConductor` that have no
Library proof at commit `314cfd1a`, numbered by their position in that
theorem. Its third premise, the variant, is proved; row 3 records the
general conductor premise of the three-premise theorem, which the route no
longer needs. The column "Five-premise position" gives the position of each
premise among those of `supercuspidalCorrespondenceHenniartFiveInputs`.
Universes are those of the full correspondence (`uK = uF`, `uW = uP`,
`uV = uA`).

The owners and states below are TaskHub task records; they are not part of
the Library commit. Rows 1 and 2 are records of 17 November 2026, row 3 and
the tasks on the chain of premise 3 below are records of 15 November 2026.
Other task states in this note are records of 14 November 2026 unless a date
is given. A candidate that is staged or under review is not a proof until it
is accepted and published.

| # | Premise (universes of the full correspondence) | Five-premise position | Module | Owner and state (TaskHub record) |
| --- | --- | --- | --- | --- |
| 1 | `Henniart.CandidateExistenceStatement.{uF, uP, uA, uP, uF}` (Henniart 2000, Thm 3.1 with §§3.7–3.8) | 1 | `Correspondence/HenniartStableMapStatement` | Task 5583 `54bed1a5-c9db-4be3-b59b-e4eb4abb89b8`, waiting; executor Worker 5732. See below; its global inputs are now pursued over totally complex number fields. |
| 2 | `Henniart.NumericalSurjectivityStatement.{uF, uP, uA}` (Henniart 1988, Thm 1.2) | 3 | `Correspondence/HenniartNumericalStatement` | Task 5584 `35ad7726-c0bc-499a-ba29-69e4bc6e3c2a`, claimed; executor Worker 5733. The proofs of Tasks 6305 and 7044, on which it waited, are in the Library. On 16 November 2026 the operator decided that it follows Option II of the operator's numerical note, and on 17 November Worker 5733 published its statement and proof tasks (Tasks 7369–7395); see premise 2 below. It has no proof candidate. |
| 3 (not needed) | `Conductor.ConductorExponentStatement.{uF, uA}` (Jacquet–Piatetski-Shapiro–Shalika 1981, Thm (5.1)) | 5 | `Representation/Conductor/EssentialStatement` | Task 5032 `7b8711bf-90dc-40ae-923e-5bfecc3550b6`, waiting; executor Worker 5032. The second executor, Worker 5731, published proof Tasks 5949 (`6cf78338-9b48-4893-a844-ba5c1273825e`) and 5950 (`85efb316-26c1-4be2-b19f-b30dbd78e2ee`) on unramified principal series and then left the task. Both are done; see below. The premise is the second conjunct of that task's target `Conductor.EssentialConductorStatement`. The route needs only its supercuspidal p-adic variant, which is proved (Task 7044); see premise 3 below. |

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
`314cfd1a` found a proof of input 3 and of none of the others. The states are
TaskHub records of 14 November 2026 unless a date is given.

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
    `lean.peer@1`; executors Workers 514 and 619), published by Worker 0,
    stated the reduction and its inputs. It proves nothing itself.
    Requirement 5 of its contract asked it to publish a focused proof task
    for the reduction statement and, for every input without a proof or a
    proof task, a proof task or a statement and planning task. Worker 514
    published Task 6702 and the planning Tasks 6698 and 6699 under it, and
    Workers 514 and 619 published the proof Tasks 6845 and 6846. Task 6413
    then published seven more tasks, listed in the table below: the proof
    Task 7213 for the reduction statement, the proof Tasks 7216, 7219 and
    7220 and the planning Tasks 7218, 7221 and 7222. The task was completed
    by 17 November 2026 (TaskHub record). The contracts of Tasks 7213 and
    7220 also ask for supporting proofs of the totally complex companions of
    their targets (units H4 under "Premise 1 over totally complex fields"
    below), and those of Tasks 7221 and 7222 ask the decomposition to cover
    them; the published targets stay primary. Task 6699 (revision 2) and Task
    6845 (revision 2) now also cover the totally complex forms of their
    targets.
  - Operator decision of 16 November 2026 (item 4 of message `681bfebb`):
    Task 7343 (`d6ca8ef3-60ca-4650-a436-8b5a00655394`, published by the
    operator) is to restate Harris 1998, Prop. 4.8, and its induction with
    the exact-stabilizer condition on the auxiliary character
    (`HasExactWeilStabilizer`) in place of general position, as new
    statements; to state the interfaces B5, B6 and B7 of the operator's plan
    note (Section 2.2) in the Library's vocabulary of weak base change; and
    to re-derive the reduction. In the restated prime branch, B6 replaces
    input 8 below, `HarrisSupercuspidalLocalComparisonStatement` (the
    comparison at a split supercuspidal place, interface A2 of the plan
    note); the singleton branch gets B5, and both branches get B7 for the
    infinity type of the output. Its deliverables include a list of which of
    the open Tasks 6702, 7213, 7216 and 7218–7222 carry over unchanged, need
    a second version or do not apply, and the consumer Task 5134 with the
    restated proposition. The present formulation, its children and the
    Drinfeld-tower branch behind input 8 stay open as the fallback; the
    contract says not to retire, revise or weaken them. The shared planning
    graph's node `proof.harris-prop48-exact-stabilizer` records the new
    branch. Its executors are Workers 390 and 514. By 02:45 UTC on 17
    November 2026 they had published three child tasks for definitions and
    statements: the exact-stabilizer datum, its validity predicates, the
    restated proposition and two inheritance statements (Task 7413,
    `afd2318f-b1bd-4392-85ce-2b4278cc4a47`); the vocabulary for B6, namely
    towers of cyclic extensions of prime degree, successive weak base
    changes along them and terminal families of Hecke characters (Task
    7417, `825a18d4-056a-4fe0-9099-4e07aa786efe`, Worker 514); and B5,
    supercuspidality descending from a cuspidal weak base change at a
    unique place, with its totally complex form (Task 7425,
    `2f5623db-ecb8-4bf0-a681-9529d6a89daf`, Worker 514). Task 7340 is to
    prove B5–B7 once they are stated. The context of Task 7417 records the
    executors' choice of B6 as in Section 2.2 of the plan note, not the
    variant of its Remark 4.2. By that context, the proof of B6 will need
    Arthur–Clozel, Ch. III, Thm 5.1, for representations induced from
    unitary cuspidal data along the tower, together with Thm III.4.2(c).
    Thm III.5.1 is also what the proof of (I4) under premise 2 needs.
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
  without added hypotheses. At commit `314cfd1a` two of the three
  hypotheses are proved, and only `AssociatedGammaStatement` is open. The
  states are TaskHub records of 14 November 2026 unless a date is given.
  - `LocalFactor.NonabelianSystem.Exists` is proved by
    `NonabelianSystem.exists_system`; see premise 2 of the five-premise
    theorem above.
  - `ClassField.Global.RelativeWeilGroup.AssociatedGammaStatement` (module
    `Automorphic/AssociatedFactorStatement`) has no Library proof. The
    published `RelativeWeilGroup.associatedGamma_of_inputs` (module
    `Automorphic/AssociatedGammaFinal`) derives
    `AssociatedGammaStatement.{u, uV, uP, uQ, uE}` from two propositions:
    `Global.CuspidalPairGlobalFunctionalEquationStatement.{u, u}` (module
    `Global/Factors/CuspidalPairFunctionalEquationStatement`) and
    `StableTwistPairGammaMatchStatement.{u, uV, uE}`. The second is proved by
    `RelativeWeilGroup.stableTwistPairGammaMatchStatement` (module
    `Automorphic/StableTwistGammaMatchProof`). So the gamma statement follows
    from the global Rankin–Selberg functional equation for cuspidal pairs
    alone. A private development check (theorem
    `associatedGamma_of_globalFE_check`, not published) composes the two
    published theorems. It compiles at commit `544dba09` with 0 errors and 0
    warnings and uses only the axioms `propext`, `Classical.choice` and
    `Quot.sound` (private diagnostic `972801ac-b28e-40a4-ba49-fae5c3deae7b`).
    The functional equation has no Library proof. Task 5493
    (`8e9a5dd6-1b51-4e53-af72-ca2e6d42fe0a`, `lean.proof@1`, waiting;
    executor Worker 5493, no candidate) is to prove it. Task 5003
    (`0fdacf55-4b2d-4416-a0bb-2c98acaa1979`, waiting; executor Worker 5003)
    is to prove the gamma statement.
  - The exhaustion of unitary generic representations,
    `Classification.UnitaryGenericExhaustion F T` (module
    `Representation/Classification/UnitaryGenericStatement`), is proved,
    since the nineteenth version, by `Classification.unitaryGenericExhaustion`
    (module `Representation/Classification/UnitaryGenericExhaustionProof`;
    Worker 4941, Task 4941 `31c91f66-6a4d-4571-9898-e0a37589a58b`, done), for
    every p-adic field `F` and every `T`, at independent universes. It applies
    the published
    `Classification.unitaryGenericExhaustion_of_tadicUnitaryDualExhaustion`
    (module `Representation/Classification/UnitaryGenericExhaustionReduction`)
    to `Classification.tadicUnitaryDualExhaustion` (module
    `Representation/Classification/TadicUnitaryDualExhaustionProof`; Worker
    4988, for Task 4988 `3fcabfac-7cbc-4d66-90b2-40b466df00f2`), which proves
    Tadić's exhaustion of the unitary dual,
    `Classification.TadicUnitaryDualExhaustion F T`, with no hypotheses. That
    proof supplies the published reduction `tadicExhaustionReduction` with
    proofs of Tadić's lemma statements, of the unitarizability of Speh
    representations (`spehUnitarizability`) and of the multisegment head
    classification. So the totally complex form of Thm 2.4 (unit B3 below)
    now waits only on that of `AssociatedGammaStatement` (unit B1), as
    Worker 4933's answer below requires.
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
  propositions. Three of them have Library proofs at commit `544dba09`:
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
- Task 3657 (`34b81620-20d7-4059-9b08-6bedd1c1c029`, verifying; executor
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
fourteen has a Library proof at commit `314cfd1a`. The owner column gives
TaskHub records: the tasks of rows 7–9 and 11–14 and their states are
records of 14 November 2026, and the tasks published from Task 6413
afterwards (rows 1–6 and 10) are records of 17 November 2026, given without
their states. The proof tasks named below require their targets at
arbitrary independent universes, which covers the universes of this table.
The reduction itself is the target of the proof Task 7213
(`b517f901-0ac4-4ae4-a08e-b8b88a3b0fec`).

| # | Input statement (universes in the reduction) | Module | Content | Owner task |
| --- | --- | --- | --- | --- |
| 1 | `Proposition48AuxiliaryRankOneStatement.{uF, uV}` | `Global/Arithmetic/HarrisProposition48AuxiliaryInputStatement` | Base case `[E' : E] = 1` of the one-place induction: realization by a Hecke character, using only the auxiliary place | Proof Task 7216 (`22c6a336-836c-47dc-bc09-667768393b20`), together with `Proposition48RankOneStatement` |
| 2 | `Proposition48AuxiliaryParityNormalizationStatement.{uF}` | same module | Correction of the inherited infinity parity by a conjugate-inverse Hecke character of the base field | Planning Task 7218 (`8a1e00f3-5223-4c5a-9994-f8f08331ceda`, `lean.peer@1`), together with the two statements of `Global/Arithmetic/HarrisProposition48ParityStatement` |
| 3 | `Proposition48AuxiliaryParityUntwistStatement.{uF, uV}` | same module | Undoing that correction on a supplied solution of the corrected problem | Planning Task 7218 |
| 4 | `Proposition48MackeyStepStatement.{uF}` | `Global/Arithmetic/HarrisProposition48MackeyStepStatement` | One prime cyclic Mackey step with all its children, of smaller normal-closure degree and inherited parity | Proof Task 7219 (`03216936-611f-40ff-9fbf-4aca7b6cec03`) |
| 5 | `Proposition48PrimeBranchStatement.{uF, uV}` | `Global/Arithmetic/HarrisProposition48PrimeBranchStatement` | Assembly of the Mackey constituents of a prime orbit | Planning Task 7221 (`528311c0-f3fd-4553-ad48-a6bed4282b5a`, `lean.peer@1`) |
| 6 | `Proposition48SingletonBranchStatement.{uF, uV}` | `Global/Arithmetic/HarrisProposition48SingletonBranchStatement` | Cyclic descent of a singleton Mackey constituent (Harris 1998, Lemma 1.6) | Planning Task 7222 (`95f79351-962f-4e98-a877-d3ca1aa759e1`, `lean.peer@1`) |
| 7 | `Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV}` | `Galois/Harris1998ExistenceStatement` | Cuspidal case of Harris 1998, Thm 1.2 | Planning Task 6698 (`cd19dd55-136e-42e9-b062-5a23b2c7a6b2`, `lean.peer@1`, ready, no executor) |
| 8 | `HarrisSupercuspidalLocalComparisonStatement.{0, 0, uV, uV}` | `Galois/HarrisSupercuspidalLocalComparisonStatement` | Equal supercuspidal components at a split place give isomorphic local Galois restrictions (derived from Harris 1999, Thm 5.9(ii)) | Proof Task 6846 (`2aa19068-4bd1-4522-8eb4-6d6a159e5e77`, `lean.proof@1`, ready, no executor). In the restated prime branch of Task 7343, B6 takes its place. |
| 9 | `CuspidalSpectralRigidityStatement.{0, uV}` | `Automorphic/Unramified/CuspidalSpectralRigidityStatement` | Mixed-rank cuspidal spectral rigidity | Proof Task 6446 (`c4f0be57-1a49-4a42-b813-4354e297ab3f`, `lean.proof@1`, ready, no executor) |
| 10 | `Proposition48IsobaricInvarianceStatement.{uV}` | `Global/Arithmetic/HarrisProposition48IsobaricInvarianceStatement` | Galois invariance of the isobaric multiset from equal Euler systems | Proof Task 7220 (`549b134f-cd9d-42ad-94bc-2d2ff16386c1`) |
| 11 | `CyclicRegularInductionStatement.{0, 0, uV, uV}` | `Automorphic/Unramified/CyclicTransferStatement` | Arthur–Clozel, Lemma III.6.4 with Thm III.6.2, in weak-induction form | Planning Task 6699 (`ca76241a-30bc-46d4-a0b9-5f6c284363a5`, `lean.peer@1`, ready, no executor) |
| 12 | `CyclicRegularOrbitLiftStatement.{0, 0, uV, uV}` | `Automorphic/Unramified/IsobaricCyclicTransferStatement` | Arthur–Clozel, Lemma III.6.4, in base-change form | Planning Task 6699 |
| 13 | `CyclicStableDescentStatement.{0, 0, uV, uV}` | `Automorphic/Unramified/CyclicTransferStatement` | Arthur–Clozel, Lemma III.6.3 | Planning Task 6699 |
| 14 | `CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV}` | `Automorphic/Unramified/CyclicWeakInductionSupercuspidalStatement` | Supercuspidality at a place of a cyclic weak induction (derived from Henniart–Herb 1995, Prop. 5.5) | Proof Task 6845 (`3064d640-8ebf-4ac1-807c-a48f48d653c4`, `lean.proof@1`, ready, no executor) |

So the reduction itself and each of the fourteen inputs now have a proof or
planning task. The operator's Task 7340 (premise 2 below) is to prove, among
other results, local automorphic induction at a non-split place (B4) and the
statements B5–B7 of Task 7343. The earlier
published statement `Global.Harris.Proposition48RankOneStatement`
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
Task 5583's draft. The second and third theorems of the composite below
avoid this transport: they fix the representation universe of the full
correspondence at `0`.

Premise 1 over totally complex fields. Henniart's globalization (Théorème 2.4
and §3) works with CM number fields and their finite extensions, which are
totally complex. So the global inputs of the reduction are needed only over
totally complex number fields.
On 15 November 2026 the operator made this the route (answer
`81ed24709e7050068786116ca6613260`, Option A). It takes the archimedean theory
of GL_n(R) off the critical path; the tasks on GL_n(R) continue. Worker 0
published five statement units under Task 0. Each states published
propositions with `[NumberField.IsTotallyComplex F]` inserted after
`[NumberField F]`, at the same universes, the rest unchanged, in a new
module. The names end in `TCStatement`. All five passed independent review
and are in the Library at commit `314cfd1a`, with the content of the
candidates below.

| Unit | Candidate | Module | Propositions |
| --- | --- | --- | --- |
| A | `aa7d05c9-a7a1-4707-a12c-adfbead2727a` | `Global/Factors/CuspidalPairFunctionalEquationTCStatement` | `Global.CuspidalArchimedeanParameterExistenceTCStatement`, `Global.CuspidalPairCompletedEquationTCStatement`, `Global.CuspidalPairGlobalFunctionalEquationTCStatement` |
| B | `ba47992f-7508-4b44-95fe-7eeaab3119e6` | `Automorphic/AssociatedFactorTCStatement` | `RelativeWeilGroup.AssociatedGammaTCStatement` (Thm 2.3), `AssociatedTemperedFactorTCStatement` (Cor. 2.3), `AssociatedSupercuspidalInductionTCStatement` (Thm 2.4), `AssociatedCuspidalFactorTCStatement` (Cor. 2.4) |
| C | `b90abaea-08af-46ad-bb64-445be3165eab` | `Global/Factors/PoleComparisonTCStatement` | `PoleComparison.RelativeCertifiedPoleComparisonsTCStatement` (Lemme 2.8), `RelativeIsometryFactorTCStatement`, `HenniartCompositeMapTCStatement` (§3.8) |
| D | `a73c39bc-cd9f-4e33-8975-7fe4b668e978` | `Correspondence/HenniartCandidateExistenceTCReductionStatement` | `Henniart.CandidateExistenceTCReductionStatement`: `CandidateExistenceReductionStatement` with inputs 2, 4 and 5 replaced by their totally complex forms; inputs 1 (Harris) and 3 unchanged |
| L | `a684ebca-ec3b-428d-b84b-62123cd1b0c6` | `Automorphic/AssociatedFactorTCReductionStatement` | the totally complex forms of three published links: `Global.CuspidalPairFunctionalEquationReductionTCStatement` (local data, A1 and A2 give A3), `RelativeWeilGroup.AssociatedGammaReductionTCStatement` (A3 at `.{u, u}` gives B1; the other input of `associatedGamma_of_inputs` is proved), `RelativeWeilGroup.AssociatedCuspidalFactorReductionTCStatement` (B3 and B2 give B4) |

A private development check, not published, proves in Lean that each
published proposition implies its totally complex form and that D's
conclusion follows from the published `CandidateExistenceReductionStatement`
(private diagnostic `d21b401e-f1ba-4319-9868-05d688041e3b`, 0 errors). It also proves links 1 and 3 from
the published proofs. Each candidate compiled with 0 errors and 0 warnings.

The operator's answer asks the owners of the existing proof tasks to stage
a proof of the totally complex form as a supporting candidate under their
current task once the statement is published. Their targets stay unchanged.
The answers that Worker 0 received on 15 November 2026 are as follows; the
row of A2 adds the Library modules published since and two reports of 17
November 2026. On 17 November 2026
Worker 0 told the owners that the statements are in the Library.

| Totally complex form | Owner task | Answer and open input of the planned proof |
| --- | --- | --- |
| A1 archimedean parameters | Task 5720 (`a2cfc970-9e20-4d56-b053-8f91a2e0b5cc`) | Worker 174: will stage. A draft proof needs only `ComplexGenericStandardParameterStatement` (Task 5977), not the GL_n(R) input (Task 5975). No answer yet from Worker 20. |
| A2 completed equation | Task 5721 (`5a3b5760-2716-4429-94f5-0ff5bf53aea8`) | Workers 5210 and 5670: will stage. It needs (G'), `Global.CuspidalPairPartialGammaEquationStatement` (Task 6190, `f4660bce-a3cb-416c-89bf-9f0cb2004c8e`), whose published reduction has two semilocal premises that include archimedean functional equations at real places (Tasks 7053 and 7054). At commit `314cfd1a` the Library has the following totally complex chain. Worker 382 (Task 6190) published the totally complex (G'), `Global.CuspidalPairPartialGammaEquationTCStatement` (module `Global/Factors/CuspidalPairPartialGammaEquationTCStatement`), the totally complex semilocal equations `RankinSelbergGlobal.UnequalSemilocalEquationTCStatement` and `EqualSemilocalEquationTCStatement` (module `Global/RankinSelberg/SemilocalEquationTCStatements`), and the proved reduction `cuspidalPairPartialGammaGlobalTCReduction` (module `Global/Factors/CuspidalPairPartialGammaGlobalTCReduction`): the eight unrestricted premises of the published reduction and the two totally complex semilocal equations imply the totally complex (G'). Two of the eight, `UnequalAnalyticStatement` and `EqualAnalyticStatement`, have Library proofs (modules `Global/RankinSelberg/UnequalAnalyticProof` and `EqualAnalyticProof`). Worker 5210 published, for Task 5721, the proved `cuspidalPairPartialGammaTCReduction` (module `Global/Factors/CuspidalPairPartialGammaTCReduction`): the totally complex (G') implies A2. Worker 44 published, for Task 7053, `UnequalSemilocalFactorizationTCStatement` and the proved `unequalSemilocalEquationTCReduction` (modules `Global/RankinSelberg/UnequalSemilocalFactorizationTCStatement` and `UnequalSemilocalEquationTCReduction`), and Worker 5557, for Task 7054, `EqualSemilocalFactorizationTCStatement` with the proved `equalSemilocalReductionTC` (module `Global/RankinSelberg/EqualSemilocalReductionTC`): each totally complex factorization premise implies the corresponding totally complex semilocal equation. Worker 5014 will prove the equal-rank factorization premise under Task 7124, from the statements of Task 7136 (executor Worker 390), whose archimedean result is stated separately for complex and for real places (module `Global/RankinSelberg/ArchimedeanSemilocalTheoryStatement`). On 17 November 2026 Worker 5014 reported to Worker 0 that the conditional reduction of the equal-rank factorization premise to statements of Task 7136 (candidate `250d6ec2`) had passed review and was awaiting integration, and that its planned totally complex form drops the real-place premise. Worker 44 (publisher of Task 7136) published on 17 November 2026 one `lean.proof@1` task for each of the four Task 7136 statements: Task 7396 (`e20c0809-5e65-47b1-892c-e19c6606624d`, `ArchimedeanCentralSignStatement`), Task 7397 (`b687b59b-c6cf-46eb-a4a9-0c9fc3bd9602`, `ArchimedeanFactorizationStatement`), Task 7399 (`a5a6c760-e1fd-47cb-80d3-eae5c19d6ed9`, `ComplexPlaceFunctionalEquationStatement`) and Task 7400 (`ad2b73ae-9f1e-45ca-88a0-3cd016a7950d`, `RealPlaceFunctionalEquationStatement`). By Worker 5014's report the first three are on the totally complex path. At commit `fcb85a7e` the Library has the four statements (modules `Global/RankinSelberg/ArchimedeanCentralSignStatement`, `ArchimedeanFactorizationStatement` and `ArchimedeanFunctionalEquationStatement`, the last with both functional equations) and their conjunctions `ArchimedeanSemilocalTheoryStatement` and `ComplexSemilocalTheoryStatement`, but not Worker 5014's reduction. |
| A3 global functional equation | Task 5493 (`8e9a5dd6-1b51-4e53-af72-ca2e6d42fe0a`) | Worker 5493: will stage, from the proofs of A1 and A2 and `cuspidalPairLocalData`. |
| B1 Thm 2.3 | Task 5003 (`0fdacf55-4b2d-4416-a0bb-2c98acaa1979`) | no answer yet. |
| B2 Cor. 2.3 | Task 5175 (`b5a124c7-ff98-4121-bd17-27c291f004d6`) | Worker 5175: will stage; a draft proof from B1 compiles. |
| B3 Thm 2.4 | Task 4933 (`65c9a94c-af88-4876-baa4-43d78ccd5531`) | Worker 4933: will stage once B1 and `UnitaryGenericExhaustion` (Task 4941) are proved. |
| B4 Cor. 2.4 | Task 5178 (`6f8aff78-c965-484e-8f71-d3ca86f6d201`) | Worker 5178: will stage. |
| C1 Lemme 2.8 | Task 6017 (`0f17fd08-105e-4659-b949-42f622d60eaa`) | Worker 406: will stage; a draft reduction from B4 compiles. |
| C2 isometry factors | Task 5191 (`c7b60e52-3b3a-45a4-a9f2-595674545493`) | Worker 5159: will stage, from B4 and B3. |
| C3 composite map | Task 5231 (`9e23a040-16d7-4a7a-bd9b-35a08938d3c4`) | no answer yet. |

D and the three links have their own `lean.proof@1` tasks, which Worker 0
published on 17 November 2026, after a TaskHub search found no task with
these targets:

- Task 7359 (`83c0699f-0ef4-46d6-ab50-724622d702a5`): link 1,
  `Global.CuspidalPairFunctionalEquationReductionTCStatement`;
- Task 7361 (`0610fbb5-7b81-4ff7-b8bf-24d14a7a0c2d`): link 2,
  `RelativeWeilGroup.AssociatedGammaReductionTCStatement`;
- Task 7362 (`7d53461b-947d-4370-9754-19e5e9a74175`): link 3,
  `RelativeWeilGroup.AssociatedCuspidalFactorReductionTCStatement`;
- Task 7363 (`a10de1f7-62b5-4acd-852f-4b0fcc13833e`): D,
  `Henniart.CandidateExistenceTCReductionStatement`.

Worker 0 expects the proof of link 2 to need totally complex copies of
`exists_engineInputs`, `commonTwistEulerInputs_families`,
`hasHeckeGammaCertificate_setups` and `associatedGamma_of_inputs`. The proof
of D is the published proof of `candidateExistenceReduction`. It needs a variant of the
globalization step that records that the number field is totally complex,
and totally complex copies of the five lemmas that pass on Théorème 2.4:
`exists_witnessedGenerator_realizeExact`,
`exists_witnessedGenerator_inducedReciprocity`,
`exists_weilImage_realizeExact_continuousInduce`,
`exists_weilImage_realizeExact_generator` and
`henniartGlobalization_of_inputs`.

D keeps Harris's Prop. 4.8 unchanged. Its fourteen-input reduction still
reaches the archimedean parameters at real places through the rigidity
input, `CuspidalSpectralRigidityStatement` (Task 6446), and the pole
statement `CuspidalPairPoleStatement` (Task 5921). Worker 3657, who published
Task 6446, answered that rigidity can also be proved by the route of
Jacquet–Shalika without archimedean parameters. That route is not stated in
the Library, and it still uses an archimedean nonvanishing result at real
places (Jacquet–Shalika I, (3.17)). On 15 November 2026 Worker 0 asked the
operator (request `99dd5c974ab65af5a036022f960632d5`) to choose between
totally complex forms of the pole statement, of input 9 and of inputs 11–14,
and that route. The operator chose the totally complex forms (answer
`d9c91a7e0fcb5cabbc936380004a4ae7`). The Jacquet–Shalika route stays
recorded as an alternative in the contexts of Tasks 6446 and 6821, with no
new statements. Worker 0 staged four statement units under Task 0, with the
same convention as A–D:

| Unit | Candidate | Module | Content |
|---|---|---|---|
| H1 | `6fa63d07-fe3c-42d2-9830-b7689151bfe9` | `Global/Factors/CuspidalPairPoleTCStatement` | `Global.CuspidalPairPoleTCStatement`; its archimedean part involves only `GL_n(ℂ)` |
| H2 | `7d11a931-f526-4e7c-87b2-9299db4cae5f` | `Automorphic/Unramified/CuspidalSpectralRigidityTCStatement` | input 9: `CuspidalSpectralRigidityTCStatement` and its three components |
| H3 | `74cbbb29-123d-410e-a4ea-29fd66b7428a` | `Automorphic/Unramified/CyclicTransferInputsTCStatement` | inputs 11–14: `CyclicRegularInductionTCStatement`, `CyclicRegularOrbitLiftTCStatement`, `CyclicStableDescentTCStatement`, `CyclicWeakInductionSupercuspidalTCStatement` |
| H4 | `7b23557e-a776-4ee5-bc88-7006d1b27625` | `Global/Arithmetic/HarrisProposition48ReductionTCStatement` | `Global.Harris.Proposition48ReductionTCStatement`, which concludes the unchanged `Proposition48Statement`, and the totally complex forms of inputs 5, 6 and 10 |

The published inputs 5, 6 and 10 take inputs 9–14 as hypotheses, so H4
restates them with the totally complex hypotheses. The prime and singleton
forms imply the published ones, and inputs 9 and 10 together imply the
totally complex form of 10. The totally complex reduction does not imply the
published one. Every field to which the reduction applies inputs 9–14 is a
CM field or a finite extension of one, hence totally complex
(`NumberField.IsCMField.isTotallyComplex`,
`NumberField.isTotallyComplex_of_algebra`). All four passed independent
review and are in the Library at commit `314cfd1a`. Worker 0 asked
Worker 3657 (publisher of Tasks 5921, 6446, 6821 and 6822) and Workers 514
and 619 (Tasks 6413 and 6699) to have totally complex proofs staged as
supporting candidates under those tasks once the statements are published.
Worker 3657 revised Tasks 5921 and 6446 to revision 2. Their contexts now
cite H1 and H2 and ask the executor to stage such a proof, which is not an
acceptance condition. The context of Task 6446 also records the
Jacquet–Shalika route; Task 6821 already names it in its objective. The
rigidity proof uses Jacquet–Shalika I (5.2)–(5.3) over the same field, and
the targets of Tasks 6821 and 6822 quantify over all number fields. Worker
3657 chose not to state totally complex forms of them. Instead, the totally
complex rigidity candidate proves them for the one field as helper lemmas:
the Landau reduction of Task 6822 works field by field, and the route of
Task 6821 through the pole statement applies it only over that field. The
candidate likewise uses only the complex-place part of the archimedean pair
regularity (target of Task 7005).

On 17 November 2026 Worker 3657 reported a draft of this proof (Task 6446,
draft revision 4; a draft, not a candidate). In it, the totally complex
rigidity follows from the totally complex pole statement H1 together with
three published statements in their unrestricted form: the boundary
nonvanishing of Shahidi (`CuspidalPairBoundaryNonvanishingStatement`, Task
5816), the archimedean pair regularity (Task 7005) and the p-adic pair
L-polynomial nonvanishing (`RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement`,
Task 6387). The draft states the pole statement over one field in a helper
module and proves the Jacquet–Shalika reductions over that field. The
executor of Task 6446 can stage it as the supporting candidate once these
inputs and the totally complex pole statement (Task 5921) are proved.

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
Lean sources at commit `544dba09` found no proof of either hypothesis. The
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
finiteness. Task 5032 was its other owner. Since 15 November 2026, Task
5584 has taken conductor finiteness from the supercuspidal p-adic variant of
premise 3 (Task 7044) instead; see premise 3 below. The
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
- Task 6305 (`44507d44-e3fd-4b88-a5cf-8efd43844948`, `lean.proof@1`) proved
  it. `Henniart.supercuspidalOrbitStratumFiniteness` (module
  `Correspondence/HenniartOrbitStratumFinitenessProof`; Lean proof by Worker
  408 from a draft by Worker 5733, candidate `ade94fc2`) proves
  `SupercuspidalOrbitStratumFinitenessStatement.{uK, uV}` at independent
  universes. It passed independent review and is in the Library at commit
  `2016a0d9`. On 15 November 2026 the task record still showed the state
  ready, with Worker 408 as executor.

The proof twists each orbit by an unramified character to a representative
whose central character is trivial at the scalar uniformizer and on the
central elements of the level-`a` subgroup. Only finitely many such central
characters exist, so each orbit meets one of finitely many sets
`SupercuspidalClass.centralLevelStratum χ a`. Each of these is finite by the
published `Henniart.CompactOpenFiniteness.centralLevelStratum_finite`
(Bernstein–Zelevinsky 1976, Cor. 4.15, for p-adic fields). This proves the
second conjunct of `NumericalOrbitCountStatement` only. The operator did not approve
the second unit proposed in the note, which would derive the counts from a
bijective numerical injection in every rank. The operator judged it circular
for this route: every known source of such an injection is a local Langlands
correspondence whose proof uses the numerical theorem. TaskHub searches on
13, 14 and 15 November 2026 found no task for the Weil-side finiteness or the
equality of the counts.

The program for the numerical step (operator decisions of 16 November
2026). Item 1 of the operator's message `681bfebb` decides that Task 5584
follows Option II of the operator's numerical note (literature source
`operator-numerical-llc-route-2026-11-16`, section "The recommended route:
Option II in detail"): Henniart's architecture, with the count on the GL
side done by simple types, without the Jacquet–Langlands correspondence and
without §7 of Henniart 1988. Worker 5733, the executor of Task 5584,
publishes the glue, the statements of the four inputs below and the
conditional assembly; the tasks for them are listed after the programs
below. The note derives the two open conjuncts of
`NumericalOrbitCountStatement`, the Weil-side finiteness and the equality of
the counts, by an elementary argument (a base case at small slopes and a
descent along a tower of cyclic extensions of prime degree) from four
inputs. In the words of the operator's plan note (source
`operator-external-inputs-plan-2026-11-16`, Section 1.3, with the interfaces
of its Section 2):

- (I1) the upper bound `|S_E(n, s, f)| ≤ ν(n, f, s; q_E)` for the number of
  unramified-twist orbits of supercuspidal classes with Swan conductor `s`
  and torsion number `f` (Bushnell–Kutzko; interface D2);
- (I2) the statement (LD): `T_E(d, s) = T_E(d + s, s)` for every p-adic
  field `E` and `1 ≤ s < d e_E`, where `T_E(d, s)` counts the
  unramified-twist orbits of irreducible `d`-dimensional Weil
  representations, irreducible on inertia, with Swan conductor `s`
  (Laumon and Deligne; interface E1, which splits into E1a, Deligne's close
  fields, and E1b, the numerical form of Laumon's local Fourier transform);
- (I3) local cyclic base change of prime degree, with its image and fibres
  on supercuspidal representations and its conductor formula
  (Arthur–Clozel; interface E2);
- (I4) the compatibility of the candidates of premise 1 with (I3)
  (interface E3): `Ch_{M/L}(Φ_L(σ)) = Φ_M(σ|_{W_M})` for irreducible `σ`,
  and `Φ_M` commutes with the action of `Gal(M/L)`.

The plan note marks the interfaces E1–E3 as still to be stated; the
statement tasks below state (I3) and (I4), and (I2) in its p-adic form.
Item 2 of the message names the proof programs, which the operator
published:

| Input | Task | Scope (from the task's objective) |
| --- | --- | --- |
| (I1), D2 | Task 7339 (`7f7277db-24f0-40f6-a94e-4abd5927739f`) | Bushnell–Kutzko simple types for GL_n over a nonarchimedean local field, as far as the numerical step needs them, and the bound (I1) for every p-adic field |
| (I3), E2 | Task 7340 (`0407c885-1c0b-496b-a8bf-829f3c1a7038`) | the simple trace formula of Deligne–Kazhdan type for GL_n over a number field with its twisted form for a cyclic extension, the local harmonic analysis on the regular elliptic set and the transfer of test functions; from them local cyclic base change of prime degree (I3), local automorphic induction at a non-split place (B4) and the statements B5, B6 and B7 |
| (I2), E1a | Task 7341 (`2009f3d2-7069-40b6-8ec4-14271918a1f1`) | the Library's Galois-side layer extended from finite extensions of `Q_p` to nonarchimedean local fields of both characteristics, and the close-fields statement E1a |
| (I2), E1b | Task 7342 (`d74e3763-4a09-4fc2-b83b-4f04643f3186`) | the numerical consequence of Laumon's local Fourier transform for a local field of characteristic `p`: equal numbers of unramified-twist orbits in the strata `W_X(d, s, f)` and `W_X(d + s, s, f)` |

None of these programs covers (I4). Its proof is global: by the plan note
(Section 2.5), it reads the candidate off the automorphic representations of
Harris's proposition and needs B1–B3 for them, C2, and the compatibility of
global base change with the local maps of E2 at the place of interest
(Arthur–Clozel, Ch. III, Thm 5.1), which the Library has not stated. On 17
November 2026 Worker 0 asked the operator who is to own the proof of (I4)
(request `c54942448c825a0ab51389153d9fba1c`); the question was still open
at 03:08 UTC that day. None of the tasks published by then under Tasks
7339–7344 or 5584 is to prove (I4).

The statement tasks of Option II. On 17 November 2026 Worker 5733 published
from Task 5584 the tasks below. Their contexts cite the operator's amendment
of that day. Each publishes definitions and Prop-valued statements in a new
module under `Langlands/Correspondence/` with the names it fixes. Tasks 7371,
7372 and 7377 are `lean.statement@1`; the others are `lean.peer@1`. None of
them proves anything, and none of their modules is in the Library at commit
`fcb85a7e`.

| Task | Module | Content |
| --- | --- | --- |
| 7369 (`cd4c8f68-81e8-434a-bc74-d3d7711bf2dd`) | `HenniartPolarPart` | the polar-part model `ν(n, f, s; q)` and `PolarPartClosedFormulaStatement`, `PolarPartCountingIdentityStatement`, `PolarPartTruncatedUniquenessStatement` |
| 7370 (`67ed0c1d-b4a2-42ea-9861-a79f84aff975`) | `HenniartRefinedStrata` | Swan exponents, torsion numbers, the refined orbit strata `W_K(n, s, f)` and `S_K(n, s, f)`, the statement `C(L, x, N)` (`Numerical.CountsAgreeUpToSlope`), `WeilArtinConductorExistenceStatement` (Artin integrality) and `RefinedStrataStatement` (the counting-versus-surjectivity lemma) |
| 7371 (`f5d725f4-f8c6-471f-8b13-2602ee6e4b01`) | `HenniartLaumonDeligneStatement` | (I2): `LaumonDeligneCountStatement`, the statement (LD) |
| 7372 (`7cc9ca0f-8675-4db1-9209-cac8b51cf753`) | `HenniartGLUpperBoundStatement` | (I1): `SupercuspidalStratumUpperBoundStatement` |
| 7373 (`4b18f9b2-c264-422a-a1b9-215f9549a7f9`) | `HenniartTwistSwanStatement` | twists by characters of `K^×` and `SupercuspidalTwistSwanBoundStatement`, `sw(χπ) ≤ max(sw π, n·sw χ)` |
| 7374 (`a058af44-6fab-4c02-9f56-ca924b697b56`) | `HenniartWeilElementaryLayer` | the truncated Weil-side counts: unramified descent, rank one, tame reduction, Henniart's Corollaire 1.4, the truncated Théorème 1.3 and the close-range count from (LD) |
| 7375 (`5fae053d-2306-4560-9d69-61d0500952a3`) | `HenniartCyclicBaseChange` | cyclic steps of prime degree `Numerical.CyclicPrimeStep`, the Herbrand function, the weak base-change predicate `Numerical.IsWeakCyclicBaseChange` and (I3): `LocalCyclicBaseChangeStatement` |
| 7376 (`88bd084f-4405-4f24-9646-699f6764fc66`) | `HenniartCompatibleInjections` | (I4): `CompatibleNumericalInjectionsStatement` |
| 7377 (`1a6c88f2-6edf-40ac-8236-a7679c30909b`) | `HenniartNumericalBaseCaseStatement` | the base case `NumericalBaseCaseStatement` at slopes below `e_L` |
| 7378 (`49809b3a-aca4-46d1-9c7c-766d60df48f5`) | `HenniartCyclicTower` | the tower lemma `CyclicTowerStatement` |
| 7379 (`3953524d-aa45-40d7-9a77-94ba97b4bac1`) | `HenniartNumericalDescentStatement` | `BaseChangeSlopeStatement`, `DescentStepStatement` and the conditional assembly `NumericalDescentStatement` |

Task 7376 states (I4) in an abstract form. For every prime `p` and every
cyclic step `S` of prime degree, with base `L` and top `M`, there are maps
`φL` and `φM` from irreducible Weil classes to supercuspidal classes over `L`
and over `M`, each a numerical injection in every rank, and a map `Ch` that
is a weak cyclic base change for `S`, such that `Ch` sends `φL(σ)` to the
image under `φM` of the decomposition of the restriction of `σ` to `W_M`
(condition (CI1) of the operator's numerical note). The statement implies
(I3) for the same `Ch`, and it does not name the Library's candidate. The
context of Task 7376 says that a proof from the candidate of premise 1 would
show that the candidate's injections satisfy (CI1) with the Arthur–Clozel base
change, and that a statement about the candidate itself can be published
later if the operator wants one.

The conditional assembly `NumericalDescentStatement.{uK, uW, uV}` (Task
7379) takes five premises and concludes `C(K, x, N)` for every p-adic field
`K`, slope `x` and rank bound `N`, together with
`NumericalSurjectivityStatement.{uK, uW, uV}` and
`NumericalOrbitCountStatement.{uK, uW, uV}`. The conductor theorem enters
through the proved `Conductor.supercuspidalPadicConductorExponent`, so it is
not a premise. The five premises and their owners on 17 November 2026:

| Premise | Statement | Proof owner |
| --- | --- | --- |
| (I1) | `SupercuspidalStratumUpperBoundStatement` (Task 7372) | program Task 7339 |
| (LD), input (I2) | `LaumonDeligneCountStatement` (Task 7371) | programs Task 7341 (E1a) and Task 7342 (E1b); the statements of the two halves wait for Task 7341's Weil groups in characteristic `p`, and the context of Task 7371 says that their statement tasks follow |
| (I4) | `CompatibleNumericalInjectionsStatement` (Task 7376) | none; operator request `c5494244` open |
| twist Swan bound | `SupercuspidalTwistSwanBoundStatement` (Task 7373) | program Task 7339, deliverable 5 (context of Task 7373) |
| Artin integrality | `WeilArtinConductorExistenceStatement` (Task 7370) | proof Task 7383 (`604237f6-a517-47b7-8581-0065c9bc6723`) |

Worker 5733 also published one `lean.proof@1` task for each statement of the
glue, Tasks 7380–7395. Among them are the proof of the conditional assembly,
Task 7395 (`cfeb9981-2abc-4b3e-ba09-a9c067679811`), the base case (Task 7394,
`b13bb2a2-e69a-413b-bb99-e4dc4d5ce67b`), the one-step descent (Task 7393,
`15dc3619-97c9-4499-8fb0-9d6176a50055`), the tower lemma (Task 7387,
`8a47ebbc-8641-4d42-8088-32ef599b0125`) and slopes under base change (Task
7388, `64326172-659a-4388-99ed-9c6456dfe542`). By 02:45 UTC on 17 November
2026, three of the operator's programs had published the following child
tasks for definitions and statements. None of them proves anything yet.

- From Task 7339, Workers 5428 and 408 published tasks for lattice chains
  and hereditary orders (`1ea54d5d-3bb3-4d8e-9163-3e4dd6ddf0c4`), cuspidal
  representations of `GL_n` over a finite field
  (`810f4d37-e331-4d03-9ae9-6e50cca61470`), the label sets of
  Bushnell–Kutzko (`55891f52-367e-41af-b895-d49870c14873`), strata and
  minimal elements (`ead706f3-8a28-4354-85bf-1a05941145b0`, Task 7412),
  simple characters (`dd46d4a2-4903-4e34-8c60-95d63a10e999`, Task 7422),
  Heisenberg representations, β-extensions and simple types
  (`36887a3d-4aab-4fb7-8e8e-df66d0ee044b`, Task 7427), and the normalized
  level with the formula that the Swan conductor of a supercuspidal is `n`
  times its level
  (`9e0c49d2-d6dc-43a5-9f51-f01cbf00506f`, Task 7419; this is the start of
  the program's deliverable 5, which the twist Swan bound needs).
- From Task 7340, its executor Worker 4918 and its collaborator Worker 5743
  published tasks for twisted conjugation
  (`67dfcf85-7b3e-4e22-acd9-64fc1a4724b3`), the norm map of Henniart–Lemaire
  (`1855760b-ecbc-4f1a-9952-566664e6d93f`), orbital and σ-orbital integrals
  on `GL_n` (`9f4ec8d0-d665-4f50-a81c-336a1d05d582`, Task 7416), the trace
  of a trace-class integral operator
  (`6f4cbfb2-ace8-4d8f-8e87-b3bb290821d2`, Task 7410), the abstract simple
  twisted trace formula (`b91648f0-f05f-466c-9977-15c80b004fc8`, Task 7420),
  and Satake characters, the unramified base-change homomorphism and the
  base-change fundamental lemma (`42d27a3e-0e30-4656-9b5c-436bf390e2a9`,
  Task 7424).
- From Task 7341, Workers 5168 and 232 published tasks that generalize to
  nonarchimedean local fields of both characteristics the Library's
  ramification filtrations (`c7768340-ef45-455e-8f55-9fafb12bfa2d`), its
  local Weil group (`82dfda3a-551b-46d6-9c6e-edbbf2ea976a`), the relative
  Herbrand function (`2139c1d7-ed11-4ca9-8eed-1989a22d0a21`, Task 7414),
  Artin and Swan conductors (`f0510851-bab0-4fb7-aec1-913aa3b78a69`, Task
  7415), and irreducible Weil classes, twists and the refined strata
  (`0569b334-d6f8-44c0-b620-42da46e763e8`, Task 7418). They also published
  tasks that state Herbrand's theorem and the properties of the upper
  filtration (`cd92a97e-84d7-4c6f-a9c1-f61a4d0f4dc5`, Task 7421), the
  independence of Artin and Swan conductors from the presentation and the
  single upper break of an irreducible Weil representation
  (`0e451702-40e0-465b-b58b-bf3207447f74`, Task 7428), and the
  correspondence between unramified-twist orbits of Weil classes and
  finite-image Galois representations
  (`b8526cc7-9056-458a-87e4-1515596580fd`, Task 7426).

So, once the glue is published and proved, premise 2 follows from the five
premises of the assembly. Of these, only (I4) has no proof owner. The
shared planning graph places the programs and the glue under premise 2:
node `proof.numerical-option-ii-orbit-count`, with
edges to `proof.simple-types-supercuspidal-bound` (Task 7339),
`proof.simple-trace-formula-local-cyclic-base-change` (Task 7340),
`proof.local-galois-both-characteristics-close-fields` (Task 7341),
`proof.laumon-numerical-statement` (Task 7342),
`proof.candidate-cyclic-base-change-compatibility` ((I4); target statement
Task 7376, no owner task) and the nodes of the glue.

Premise 3. The route no longer needs this premise of the three-premise
theorem: the two-premise entry above uses its supercuspidal p-adic variant,
which is proved (Task 7044; see the end of this section). This section
records the general statement, its chain and the variant for reference.
`Conductor.ConductorExponentStatement` has no Library proof at commit
`314cfd1a`; Task 5032 owns it. The published
`Conductor.conductorExponentStatement_of` (module
`Representation/Conductor/EssentialConductorReduction`) derives it from five
hypotheses. Since the sixteenth version, four of them follow from published
theorems:

- `Whittaker.MirabolicRestrictionInjectivityStatement` is proved by
  `Whittaker.mirabolicRestrictionInjectivity` (module
  `Representation/Whittaker/MirabolicRestrictionInjectivityProof`).
- `Conductor.TrivialCharacterEpsilonStatement` is proved by
  `Conductor.trivialCharacterEpsilon` (module
  `Representation/Conductor/TrivialCharacterEpsilonProof`).
- `Conductor.EssentialDualComparisonStatement` (JPSS 1981, (5.3)) is proved
  by `Conductor.essentialDualComparison` (module
  `Representation/Conductor/EssentialDualComparisonProof`; Lean proof by
  Worker 5548, for Task 5548, `9997abfc-1e29-4737-85d0-3b354868d773`), new
  since the sixteenth version. It applies
  `Conductor.essentialDualComparison_of_functionalEquation` (module
  `Representation/Conductor/EssentialDualComparisonBridge`) to mirabolic
  injectivity and to the corank-one spherical functional equation, which
  `Conductor.sphericalCorankOneFunctionalEquation` (module
  `Representation/Conductor/SphericalCorankOneFunctionalEquationProof`; Task
  5680, `685d39c3-c280-41e2-bdd5-6012dd1d2339`, done) proves for every
  nonarchimedean local field.
- `Conductor.ConductorMinimalityStatement` is proved by
  `Conductor.conductorMinimalityStatement` (module
  `Representation/Conductor/ConductorMinimalityProof`; Lean proof by Worker
  5549, for Task 5549, candidate `262dddae-922f-4099-99da-bc79de5c8c2d`), new
  at commit `fab9caea`. The proof composes two published theorems.
  `Conductor.conductorMinimalityStatement_of_sphericalFunctionalEquation`
  (module `Representation/Conductor/ConductorMinimalityReduction`) derives it
  from `Conductor.SphericalLaurentFunctionalEquationStatement` and mirabolic
  injectivity. `Conductor.sphericalLaurentFunctionalEquation` (module
  `Representation/Conductor/SphericalLaurentFunctionalEquationProof`; Task
  5777, candidate `0377660e-2370-4784-8811-274ae4be1081`, Lean proof by
  Worker 95), new since the sixteenth version, proves that statement with no
  hypotheses. It applies
  `Conductor.sphericalLaurentFunctionalEquation_of_corankOne_of_laurent`
  (module `Representation/Conductor/SphericalLaurentFunctionalEquationReduction`)
  to the corank-one functional equation and to the published
  `Conductor.sphericalCorankOneLaurent` (module
  `Representation/Conductor/SphericalCorankOneLaurentProof`).

The fifth hypothesis, `Conductor.EssentialVectorExistence` (defined in the
reduction module; the existence half of Jacquet 2012, Theorem 1), is the
only one left. A search of the Lean sources at commit `544dba09` found no
unconditional proof of it. It is part of the first conjunct,
`Conductor.EssentialVectorStatement`, of Task 5032's target
`Conductor.EssentialConductorStatement`. A search of the TaskHub task
contracts for its name found only review tasks, so no other task has it as
its target.

Published theorems derive `EssentialVectorExistence` from the generation
statement `Conductor.OrderedUnramifiedCorankOneGenerationStatement` (module
`Representation/Conductor/OrderedUnramifiedCorankOneGenerationStatement`,
Worker 8). Its Markdown attributes it to Jacquet 2012, Lemma 3, which quotes
Jacquet–Piatetski-Shapiro–Shalika 1983, where it is part of the Proposition
of §(9.4) (printed p. 458, displays (3)–(4)), which uses §(8.4). For a
generic representation π of `GL_(n+2)(F)` with L-polynomial `P`, and an
unramified principal series `I(x)` of `GL_(n+1)(F)` whose parameters have
nondecreasing norms, it says that a finite sum of corank-one integrals,
multiplied by `∏_i P(x_i q^(-s))`, equals 1 on a right half-plane.
`Conductor.sphericalLFactorGeneration_of_generation` (module
`Representation/Conductor/SphericalLFactorGenerationAssembly`) derives
`Conductor.SphericalLFactorGenerationStatement` from it, and
`Conductor.exists_isEssentialVector_of_jpss` (module
`Representation/Conductor/EssentialExistenceReduction`) gives an essential
vector of one representation from the conclusions of
`SphericalLFactorGenerationStatement` for that representation. Applied to
every representation, these give `EssentialVectorExistence`.

Private development checks, not published, compose these published theorems
in one module. Its theorem `conductorExponent_of_essentialVector_check`
proves `ConductorExponentStatement.{uF, uV}` from
`EssentialVectorExistence.{uF, uV}` alone, and its theorem
`conductorExponent_of_generation_check` proves it from
`OrderedUnramifiedCorankOneGenerationStatement.{uF, uV}` alone. The module
compiles at commit `544dba09` with 0 errors and 0 warnings. For each of the
two theorems, the service's declaration inspection lists only the axioms
`propext`, `Classical.choice` and `Quot.sound` (private diagnostics
`4d087b22-e14e-44bb-bc28-0adea610068a` and
`71a3fcb4-6f56-4b8c-9d52-a32b0abf62e0`).

The tasks on this chain, with their TaskHub records of 15 November 2026:

- Task 5032 (`7b8711bf-90dc-40ae-923e-5bfecc3550b6`, waiting; executor
  Worker 5032) owns premise 3, as in the table.
- Task 5549 (`187e708b-4c2c-40b4-9ddd-8ca35e07fdd0`, `lean.proof@1`, done)
  proved `ConductorMinimalityStatement` as a theorem of its own; see the
  list above.
- Task 5878 (`d06ea375-9c2e-4a40-9fe4-ae54f3fcec36`, `lean.proof@1`, revision
  2, waiting; executor Worker 8) is to prove
  `SphericalLFactorGenerationStatement`. With
  `exists_isEssentialVector_of_jpss`, a proof would give
  `EssentialVectorExistence`. Its executor's question to the operator,
  `8c5d5099530a5576aa6b411cf94016d8`, names the generation statement as the
  task's last open input.
- On 13 November 2026 (23:27 UTC) the operator deferred the generation
  statement. Item 5 of the operator's answer
  `092b33b7ccc353ae87e8d7c545221493` to Worker 8
  defers the ordered-unramified L-product for generic π (JPSS 1983, (9.4)
  and (8.4)) and says not to publish it yet. The same answer lists the
  classification batch for (9.4) and (8.4) as out of scope until the operator
  decides. Worker 8's question
  `8c5d5099530a5576aa6b411cf94016d8` asked the operator to lift this
  deferral. The operator answered it on 15 November 2026 (00:04 UTC, answer
  `dcb4e51b4b6954b9836fcbf50ec92c05`) with Option C: the deferral stays, no
  task is to be published for `OrderedUnramifiedCorankOneGenerationStatement`,
  the all-field port of the (9.4)/(8.4) classification batch is not to be
  started until the operator decides on full generality, and Task 5878 stays
  paused until then. The same answer refers to the supercuspidal p-adic
  variant below, and says that Task 5032 stays blocked meanwhile.

Use of the premise in the route. A reading of the Lean sources at commit
`544dba09`, not a Lean-checked statement, shows that the route uses premise 3
only for supercuspidal representations over p-adic fields. In the published
reductions above, every occurrence of the premise passes it on, except one:
`Henniart.Extension.exists_newvectorConductor_of_pairEpsilon` (module
`Correspondence/HenniartConductorFinitenessProof`) applies
`Conductor.genericConductor_isNewvectorConductor_of_conductorExponentStatement`
(module `Representation/Conductor/GenericEpsilonConductor`) to a supercuspidal
representation `A : GeneralLinear.SupercuspidalRep (F := K.Carrier) (n := k + 1)`
of a p-adic field `K`. The three-premise theorem reaches it through
`surjectivityStepReduction` (by way of `rankExtension_conductor` and
`conductor_eq_of_pairEpsilon`, module `Correspondence/HenniartRankConductor`)
and through `supercuspidalEpsilonConductorFinitenessPadicReduction`.

On 14 November 2026 Worker 0 asked the operator (question
`8457135d67325c5580f35738976b03b6`) whether to publish, under Task 0, a
variant of premise 3 restricted to supercuspidal representations over p-adic
fields, a reduction statement for the three-premise theorem with that variant
in place of premise 3, and proof tasks for both. On 15 November 2026 the
operator approved this (answer `b7d128c427d25d6395cc179a019a008c`), with
conditions: the statements go into new modules; their Markdown cites
JPSS 1981, Théorème (5.1), and JPSS 1983, Theorem (2.7) and §(8.1); Tasks
5032 and 5878 and the deferral above stay unchanged; Worker 8 stays paused.
The two proof tasks are to be published after both statements are published.
Worker 0 submitted both statements on 15 November 2026. Both passed
independent review and are in the Library at commit `fab9caea`:

- `Conductor.SupercuspidalPadicConductorExponentStatement` (module
  `Representation/Conductor/SupercuspidalPadicConductorExponentStatement`;
  candidate `33a4c5cd-f5bf-4514-a42d-99c2ae6dfcad`). It is
  `ConductorExponentStatement` for the field `K.Carrier` of a p-adic field
  `K`, with the added hypothesis
  `GeneralLinear.IsSupercuspidal π`. It gives `K.Carrier` its canonical
  topology, valuation and local-field structure, as the route's call site
  does. The canonical structures were chosen because two published results
  that the planned proof needs are stated for them:
  `RankinSelberg.supercuspidalUnequalRankLFactor` (JPSS 1983, §(8.1),
  Proposition (i)) and `Langlands.supercuspidalKirillov`.
- `Henniart.Extension.SupercuspidalCorrespondenceHenniartSupercuspidalConductorStatement`
  (module `Correspondence/HenniartSupercuspidalConductorReductionStatement`;
  candidate `5c39acfe-39fc-45f4-99b4-417e877c6fa3`). It is the published
  three-premise statement with premise 3 replaced by the variant. It imports
  the variant's module.

A private development check, not published, proves in Lean that
`ConductorExponentStatement` implies the variant. It also proves that the
variant gives the conclusion of
`genericConductor_isNewvectorConductor_of_conductorExponentStatement` for a
supercuspidal representation, with the instances of
`GenericEpsilonConductor` (private diagnostic
`be50c246-626b-41da-bec9-b41b4b1d7d46`, 0 errors).

The variant is proved: `Conductor.supercuspidalPadicConductorExponent`
(module `Representation/Conductor/SupercuspidalPadicConductorExponentProof`;
Worker 388, Task 7044; in the Library at commit `72480b70`) proves
`SupercuspidalPadicConductorExponentStatement.{uF, uV}` at independent
universes. Its Markdown describes the proof. Rank one is Tate's local theory
(the published `GodementJacquet.localTateConductor` with
`Conductor.conductorExponent_rankOne_of_localTate`). In rank at least 2 the
proof follows the published `Conductor.conductorExponentStatement_of`. The
existence of essential vectors is supplied for supercuspidal representations
by the helper `SupercuspidalPadic.exists_isEssentialVector` (module
`Representation/Conductor/SupercuspidalPadicEssentialExistence`), which uses
the fact that a supercuspidal representation has L-factor 1. It uses neither
`Conductor.EssentialVectorExistence` nor the deferred generation statement.
The reduction (Task 7045) is proved as well, so the supercuspidal
correspondence follows from premises 1 and 2 alone.

Worker 0 published the two proof tasks on 15 November 2026:

- Task 7044 (`601c1ed8-5f29-4316-a599-67730ec900fd`, `lean.proof@1`) is to
  prove `Conductor.SupercuspidalPadicConductorExponentStatement`. Its proof
  is published (above).
- Task 7045 (`91b1a919-c763-40e4-b0e7-3ee049060243`, `lean.proof@1`) is to
  prove
  `Henniart.Extension.SupercuspidalCorrespondenceHenniartSupercuspidalConductorStatement`
  by adapting the published route theorems in new modules. Its proof by
  Worker 619 is in the Library since commit `a98af0ff`, and the task is
  completed; see "Published: the two-premise entry".

Following the operator's instruction (message
`3187b6ad4bdc53ae968332d07f4669e3`), Worker 0 asked the executors of Tasks
4803 and 5584 to wait on these tasks instead of Task 5032. Worker 4803
confirmed that Task 4803 now waits on Tasks 5583, 5584, 7044 and 7045, and
no longer on Task 5032. Its final assembly will apply the Task 7045 theorem
to the theorems of Tasks 5583, 5584 and 7044. Of these four tasks, Tasks
7044 and 7045 now have published proofs; Task 4803 was waiting on 17
November 2026 (TaskHub record). Worker 5733 confirmed that
Task 5584 now waits on Task 7044 instead of Task 5032; its wait on Task 6305
stays, although the proof of Task 6305 is now published (premise 2 above).
Its need was a published proof of the variant at arbitrary universes, which
the proof of Task 7044 provides.

Task 5584 also uses the conductor finiteness of supercuspidal classes, the
second hypothesis of `numericalOrbitReduction` under premise 2 above. A
private development check, not published, proves in Lean that the variant
implies this hypothesis. The check obtains a nontrivial additive character
from `padicUnitaryAdditiveCharacterExists`, scales it to conductor `O` by
`UnramifiedUnitary.exists_scale_hasIntegerConductor`, and gets genericity from
`SupercuspidalLFactorCharacterization.isGeneric_of_isSupercuspidal`. It then
applies the variant and `Extension.firstFixedLevel_eq_of_isNewvectorConductor`.
With `numericalOrbitReduction`, it derives `NumericalSurjectivityStatement`
from `NumericalOrbitCountStatement` and the variant. It compiles at commit
`fab9caea` with 0 errors and 0 warnings. The service's declaration inspection
lists only the axioms `propext`, `Classical.choice` and `Quot.sound` (private
diagnostic `431640be-f288-43fa-b590-dc325f3b88ff`). Worker 5733 compiled the
same code in a private draft of Task 5584 with the same result.

The two proof tasks that Worker 5731 published from Task 5032 are done. Their targets are the two conjuncts of
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

## Operator decisions of 16 November 2026

The operator's message `681bfebbe78e534fb445d97c189108c7` to Worker 0 records
six decisions and asks that they be recorded here and placed in the shared
planning graphs. The operator published the new tasks named below. The
other recommendations of the operator's plan note are guidance, not
decisions.

1. The numerical step: Task 5584 follows Option II; see premise 2 above.
2. Proof programs for the inputs of Option II: Tasks 7339, 7340, 7341 and
   7342; see premise 2 above.
3. The port of the NYLL library is stopped. Its three targets, the
   conjuncts `FiniteAbelianReciprocity`, `FiniteAbelianNormTransfer` and
   `FiniteAbelianRestriction` of
   `LocalClassField.FiniteAbelianReciprocityTheorems` (module
   `ClassFieldTheory/Local/FiniteReciprocityStatement`), follow from the
   Library's own finite Artin symbol; Task 7335
   (`934a16de-d459-457a-a7cb-cde3d4238eb5`, `lean.proof@1`) is to prove
   them (planning node `proof.finite-abelian-reciprocity-library-symbol`).
   The operator retired the 186 open port tasks, among them Tasks 923–929.
   Thirteen port tasks stay open only until the candidates they have in
   integration are published. The published port modules stay in the
   Library. The port is not to be reopened and its units are not to be
   republished (plan note, Section 5.1).
4. Harris's Prop. 4.8: Task 7343 restates it under the exact-stabilizer
   condition; the present formulation stays as the fallback. See input 1 of
   premise 1 above.
5. Group F of the plan note (arithmetic tools). Task 7344
   (`45301eed-f9e6-4bb4-a6ac-a0de8f0deb35`) is to prove the Library's
   `ChebotarevPrimeRealizationStatement` by turning the audited private
   adaptation of the Chebotarev closure of the Anthropic FLT repository
   (Library note `notes/reuse/anthropic-chebotarev-audit.md`) into a
   reviewed port, and to derive `FiniteGaloisFrobeniusRigidityStatement` and
   `ChebotarevRigidityStatement` from it. Task 7345
   (`d60e084d-9218-49be-9468-da445fab6919`) is to decide how the five
   clauses of `FiniteAbelianClassFieldStatement` are to be obtained, by
   listing their consumers and auditing NYLL's global class field theory,
   and to report to the operator. The planning graph's nodes
   `proof.finite-galois-chebotarev-rigidity` and
   `proof.finite-abelian-global-reciprocity` name these tasks. Under Task
   7344, Worker 46 published the proof task for
   `ChebotarevPrimeRealizationStatement` (Task 7411,
   `4a813bfb-73ed-4116-ae47-a1f477f02373`), and a sibling proof task for
   `FiniteGaloisFrobeniusRigidityStatement`, from that statement and the
   finite character theorem, was published as its deliverable 3a (Task
   7408, `e1a8ad15-88cb-491e-b31f-6ccafd903bef`). By the plan
   note (Section 2.6), the route uses Chebotarev's theorem to pass from
   equal Frobenius traces at almost all places to isomorphic semisimple
   Galois representations and to choose auxiliary primes.
6. The operator retired six unstarted tasks whose targets are already
   Library theorems: Tasks 5173, 6568, 6638, 7010, 7161 and 7162. None of
   them is named elsewhere in this note.

## Tasks that left the route

The route no longer needs premise 3 of the three-premise theorem,
`Conductor.ConductorExponentStatement`, owned by Task 5032
(`7b8711bf-90dc-40ae-923e-5bfecc3550b6`): the two-premise entry uses its
supercuspidal p-adic variant, proved by Task 7044, and the reduction of Task
7045 is proved. Neither Task 5032 nor Task 5878
(`d06ea375-9c2e-4a40-9fe4-ae54f3fcec36`) is on the route any more. The
operator's conditions of 15 November 2026 stay in force: Tasks 5032 and
5878 and the deferral of the generation statement stay unchanged, and
Worker 8 stays paused (premise 3 above). The statement remains the second
conjunct of the target of Task 5032.

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
`fcb85a7ef43356fec01e6ccf1605f08568c08cb0` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with 0 errors and 0 warnings. The
check compiled the block verbatim as a private draft module in the Lean
service, together with a second draft module that imports it and runs
`#print axioms` on its three theorems. The service's declaration inspection
was run once for each theorem; each lists only the axioms `propext`,
`Classical.choice` and `Quot.sound`. The diagnostics are the private records
`5ec0c345-93c1-4658-ab8a-6b56a08c7039` (first theorem),
`d11cf522-aafa-4fed-ade8-71a5f3eecae2` (second theorem) and
`61df03da-8359-4075-8e00-78632e90c3c3` (third theorem). To reproduce them,
save the block as a draft module and compile it with `lean_check`, naming
each theorem as the declaration to inspect. The module is a development
check, not a published proof.

The first theorem, `fullCorrespondence_of_henniartTwoInputs`, has the two
open premises as its hypotheses, in the order of the table. It applies the
published `Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor`
(Task 7045) to these two hypotheses and to the published
`Conductor.supercuspidalPadicConductorExponent` (Task 7044), and then the
published `fullCorrespondenceStatement_of_supercuspidalCorrespondence`. The
eighth to nineteenth versions had in its place the three-premise theorem
`fullCorrespondence_of_henniartThreeInputs`, which applied
`supercuspidalCorrespondenceHenniartThreeInputs` and also assumed the
general conductor exponent statement `Conductor.ConductorExponentStatement`.
The eighth version's proof applied
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
in these four hypotheses. Premise 2 is a hypothesis at `uA = 0`. Up to the
nineteenth version the theorem also assumed the general conductor exponent
statement at `uA = 0`. The theorem does not prove the target at an arbitrary
universe `uA`; Task 5583 owns that passage (see premise 1 above).

The third theorem, `fullCorrespondence_zero_of_henniartTCInputs`, is new in
this version. It has the same conclusion and also applies the first theorem
at `uA = 0`. It obtains premise 1 at the same universes from its hypothesis
`hD`, the published proposition
`CandidateExistenceTCReductionStatement.{uF, uP, uS, uP, uF}` (statement D
above, module `Correspondence/HenniartCandidateExistenceTCReductionStatement`),
applied to `localRelativeClassFormation.{0}` and to four further hypotheses.
These are Harris's Prop. 4.8 in its present Library form,
`Global.Harris.Proposition48Statement`, at the same universes as in the second
theorem, and the totally complex forms of Henniart's Thm 2.4, Lemme 2.8 and
§3.8: `AssociatedSupercuspidalInductionTCStatement` (module
`Automorphic/AssociatedFactorTCStatement`) and
`RelativeCertifiedPoleComparisonsTCStatement` and
`HenniartCompositeMapTCStatement` (module
`Global/Factors/PoleComparisonTCStatement`). Premise 2 is a hypothesis at
`uA = 0`. The hypothesis `hD` is the target of the proof Task 7363; a Library
proof of it would leave the four global hypotheses and premise 2. Like the
second theorem, the third does not prove the target at an arbitrary universe
`uA`.

```lean
import Langlands.Correspondence.FullCorrespondenceReduction
import Langlands.Correspondence.HenniartSupercuspidalConductorReductionProof
import Langlands.Representation.Conductor.SupercuspidalPadicConductorExponentProof
import Langlands.Correspondence.HenniartCandidateExistenceReductionProof
import Langlands.Correspondence.HenniartCandidateExistenceTCReductionStatement
import Langlands.ClassFieldTheory.Local.LocalRelativeClassFormationProof

namespace Langlands.Correspondence

universe uF uP uA uS

open Langlands.Henniart LocalFactor in
/-- The full correspondence from the two premises of Henniart's route that the Library does
not prove: candidate existence and numerical surjectivity. The conductor premise is supplied
in its supercuspidal p-adic form by the published `Conductor.supercuspidalPadicConductorExponent`
(Task 7044), through the published `supercuspidalCorrespondenceHenniartSupercuspidalConductor`
(Task 7045). -/
theorem fullCorrespondence_of_henniartTwoInputs
    (hCE : CandidateExistenceStatement.{uF, uP, uA, uP, uF})
    (hnum : NumericalSurjectivityStatement.{uF, uP, uA}) :
    FullCorrespondenceStatement.{uF, uP, uA} :=
  fullCorrespondenceStatement_of_supercuspidalCorrespondence
    (Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor.{uF, uP, uA} hCE hnum
      Conductor.supercuspidalPadicConductorExponent.{uF, uA})

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
    (hnum : NumericalSurjectivityStatement.{uF, uP, 0}) :
    FullCorrespondenceStatement.{uF, uP, 0} :=
  fullCorrespondence_of_henniartTwoInputs.{uF, uP, 0}
    (candidateExistenceReduction.{uF, uP, uS, uP, uF} hHarris hasi
      ClassFieldTheory.Local.localRelativeClassFormation.{0} hpole hcomp)
    hnum

open Langlands.Henniart LocalFactor in
/-- Totally complex variant: candidate existence from the published totally complex reduction
statement `CandidateExistenceTCReductionStatement` (Task 7363 is to prove it), Harris's
Prop. 4.8 and the totally complex forms of Henniart's Thm 2.4, Lemme 2.8 and §3.8. -/
theorem fullCorrespondence_zero_of_henniartTCInputs
    (hD : CandidateExistenceTCReductionStatement.{uF, uP, uS, uP, uF})
    (hHarris : Global.Harris.Proposition48Statement.{uF, 0, 0, 0, uS})
    (hasi : ClassField.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionTCStatement.{0, uP, uS, uS})
    (hpole : Global.PoleComparison.RelativeCertifiedPoleComparisonsTCStatement.{0, uP, uS})
    (hcomp : Global.PoleComparison.HenniartCompositeMapTCStatement.{0, uF, uP, uS, uP})
    (hnum : NumericalSurjectivityStatement.{uF, uP, 0}) :
    FullCorrespondenceStatement.{uF, uP, 0} :=
  fullCorrespondence_of_henniartTwoInputs.{uF, uP, 0}
    (hD hHarris hasi ClassFieldTheory.Local.localRelativeClassFormation.{0} hpole hcomp)
    hnum

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
