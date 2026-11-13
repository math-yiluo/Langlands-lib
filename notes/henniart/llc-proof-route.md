# Local Langlands for GL_n: published reductions and the remaining premises

Author: Worker 0, for Task 0 (`69dd20b3-6a77-44aa-b779-32391843c8dd`). First
version 10 November 2026, second version 11 November 2026, third, fourth and
fifth versions 12 November 2026, sixth and seventh versions 13 November 2026.
This eighth version, also of 13 November 2026, was checked against Library
commit `9b849caba7c63ede041b7fec49c90ceaafb08568`.

This note records how the published Library reduces the full local Langlands
correspondence for GL_n to three propositions, and names the task that owns
each of them. The newest published reduction,
`Henniart.Extension.supercuspidalCorrespondenceHenniartFiveInputs`, has five
premises. The seventh version listed all five as open. Since then the Library
has proved two of them: the existence of local constants, by
`LocalFactor.NonabelianSystem.exists_system`, and rank-one conductor transport
in the common closure, by
`LocalFactor.SpectralConductor.commonClosureRankOneConductor`. Three premises
therefore remain open. The composite Lean module below assembles the published
theorems. It has been compiled as a development check but is not published.
Each of the three open propositions still needs an accepted `lean.proof@1`
candidate. For statement meanings and sources see
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
  fifth theorem, applies the fourth, and
  `Henniart.Extension.supercuspidalCorrespondenceHenniartFiveInputs`, the
  sixth, applies the fifth; see the next three sections.

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
have Library proofs. The note numbers premises by their position in that
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
  (module `ClassField/Global/LocalRelativeWeilTransferProof`, Task 5086, done).
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

## The three open premises

The table lists the three premises of
`supercuspidalCorrespondenceHenniartFiveInputs` that have no Library proof at
commit `9b849cab`, numbered by their position in that theorem, at the
universes of the full correspondence (`uK = uF`, `uW = uP`, `uV = uA`).

The owners and states below are TaskHub task records as inspected on
13 November 2026; they are not part of the Library commit. A candidate that is
staged or under review is not a proof until it is accepted and published.

| # | Premise (universes of the full correspondence) | Module | Owner and state on 13 November 2026 |
| --- | --- | --- | --- |
| 1 | `Henniart.CandidateExistenceStatement.{uF, uP, uA, uP, uF}` (Henniart 2000, Thm 3.1 with §§3.7–3.8) | `Correspondence/HenniartStableMapStatement` | Task 5583 `54bed1a5-c9db-4be3-b59b-e4eb4abb89b8`, waiting; executor Worker 5732. See below. |
| 3 | `Henniart.NumericalSurjectivityStatement.{uF, uP, uA}` (Henniart 1988, Thm 1.2) | `Correspondence/HenniartNumericalStatement` | Task 5584 `35ad7726-c0bc-499a-ba29-69e4bc6e3c2a`, waiting; executor Worker 5733. It has no proof candidate; its route-study note is published. See below. |
| 5 | `Conductor.ConductorExponentStatement.{uF, uA}` (Jacquet–Piatetski-Shapiro–Shalika 1981, Thm (5.1)) | `Representation/Conductor/EssentialStatement` | Task 5032 `7b8711bf-90dc-40ae-923e-5bfecc3550b6`, waiting; executor Worker 5032. The second executor, Worker 5731, published proof Tasks 5949 (`6cf78338-9b48-4893-a844-ba5c1273825e`) and 5950 (`85efb316-26c1-4be2-b19f-b30dbd78e2ee`) on unramified principal series and then left the task. The premise is the second conjunct of that task's target `Conductor.EssentialConductorStatement`. |

Premise 1. The operator decided on 13 November 2026 that Task 5583 keeps its
unconditional target unchanged. Its global inputs are owned by other tasks,
and its executor waits on them: Tasks 5228
(`3562e8a2-a9cf-412d-959f-04f43884373c`), 5230
(`2a08796a-fc06-4ed1-ab5a-7751da0b394b`) and 5231
(`9e23a040-16d7-4a7a-bd9b-35a08938d3c4`), which prove the parts and the
assembly of `HenniartCompositeMapStatement`; Task 5191
(`c7b60e52-3b3a-45a4-a9f2-595674545493`, `RelativeIsometryFactorStatement`,
including the certified pole comparisons); Task 4933
(`65c9a94c-af88-4876-baa4-43d78ccd5531`, Henniart's local induction from
unitary supercuspidals for associated pairs); Task 5134
(`1b87b965-a232-4c02-a51f-e287f630c549`, Harris 1998, Prop. 4.8 implies
`HenniartGlobalizationStatement`); and Task 3657
(`34b81620-20d7-4059-9b08-6bedd1c1c029`, the global program and its
conditional assembly). The transport of supercuspidal unitary lattices between
carrier universes, which the globalization in universe 0 makes necessary, is a
helper in Task 5583's draft.

Premise 3. Task 5891 (`e69d09d4-6da8-4810-886b-664574e533f8`, done) proved
the counting reduction of Henniart 1988, §2.8, in orbit form:
`Henniart.numericalOrbitReduction` (module
`Correspondence/HenniartNumericalReductionProof`; Lean proof by Worker 5733,
checked by Worker 5428) proves `Henniart.NumericalOrbitReductionStatement`. That
statement says that `NumericalSurjectivityStatement` follows from two
hypotheses: `NumericalOrbitCountStatement` (for every p-adic field, rank and
conductor, the unramified-twist orbit strata on the Weil and supercuspidal
sides are finite and have equal cardinality), and finiteness of the conductor
`Numerical.conductor K π` of every supercuspidal class `π`. A search of the
Lean sources at commit `9b849cab` found no proof of either hypothesis. The
operator decided on 13 November 2026 that Task 5584 stays open and that its executor does not prove conductor
finiteness of supercuspidal classes: that is owned through Task 5585
(`5da7d945-39ed-4dcb-ace6-030fa18e4f24`, Bernstein–Zelevinsky 1976,
Cor. 4.15; ready, with no executor on 13 November 2026) and Task 5032. The
executor of Task 5584 wrote a route-study note,
[Henniart's numerical correspondence: route study for the orbit counts](numerical-count-route-study.md),
which compares Henniart's 1988 route to the orbit counts with a route through
explicit counts. A TaskHub search on 13 November 2026 found no separate proof
task for `NumericalOrbitCountStatement`.

## Tasks that left the route

The seventh version listed premise 2, owned by Task 4913, and premise 4, owned
by Task 5815, as open. Both are now proved, as described above, and both tasks
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
and premise 4, both now proved, so the route no longer needs Task 5626. The
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
field, including fields of positive characteristic, and remains Task 5585's
target.

## The composite

The module below compiles at commit
`9b849caba7c63ede041b7fec49c90ceaafb08568` in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, with 0 errors and 0 warnings. The
check compiled the block verbatim as a private draft module in the Lean
service; its diagnostics are private records (`497dc066-d224-44d4-9624-0837d81ad14a`
for the build, `ebc3eabc-21af-4ea2-8dd7-4446ba736e63` for the declaration
inspection). To reproduce it, save the block as a draft module and compile it
with `lean_check`. The declaration inspection of
`fullCorrespondence_of_henniartThreeInputs` reports only the axioms `propext`,
`Classical.choice` and `Quot.sound`. All four theorems it applies are
published: `fullCorrespondenceStatement_of_supercuspidalCorrespondence`,
`supercuspidalCorrespondenceHenniartFiveInputs`,
`NonabelianSystem.exists_system` and
`SpectralConductor.commonClosureRankOneConductor`. Its hypotheses are the three
open premises, in the order of the table. The seventh version's composite,
`fullCorrespondence_of_henniartFiveInputs`, also assumed premises 2 and 4. The
sixth version's composite, `fullCorrespondence_of_henniartRankOneInputs`,
assumed refinement invariance as well.

```lean
import Langlands.Correspondence.FullCorrespondenceReduction
import Langlands.Correspondence.HenniartCorrespondenceFiveInputs
import Langlands.LocalFactor.NonabelianSystemExistsProof
import Langlands.LocalFactor.SpectralConductorRankOneProof

namespace Langlands.Correspondence

universe uF uP uA

open Langlands.Henniart LocalFactor LocalFactor.CommonClosure in
/-- The full correspondence from the three premises of
`supercuspidalCorrespondenceHenniartFiveInputs` that the Library does not prove:
candidate existence, numerical surjectivity and the JPSS conductor exponent. The
local-constant systems and rank-one conductor transport are supplied by the published
`NonabelianSystem.exists_system` and `SpectralConductor.commonClosureRankOneConductor`. -/
theorem fullCorrespondence_of_henniartThreeInputs
    (hCE : CandidateExistenceStatement.{uF, uP, uA, uP, uF})
    (hnum : NumericalSurjectivityStatement.{uF, uP, uA})
    (hJPSS : Conductor.ConductorExponentStatement.{uF, uA}) :
    FullCorrespondenceStatement.{uF, uP, uA} :=
  fullCorrespondenceStatement_of_supercuspidalCorrespondence
    (Extension.supercuspidalCorrespondenceHenniartFiveInputs.{uF, uP, uA}
      hCE (fun _ _ K eC => NonabelianSystem.exists_system.{uF, uP} K eC) hnum
      SpectralConductor.commonClosureRankOneConductor.{uF} hJPSS)

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
