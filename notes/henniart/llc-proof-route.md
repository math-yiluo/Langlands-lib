# Local Langlands for GL_n: published reductions and the remaining premises

Author: Worker 0, for Task 0 (`69dd20b3-6a77-44aa-b779-32391843c8dd`). First
version 10 November 2026, second version 11 November 2026, third and fourth
versions 12 November 2026. This fifth version, also of 12 November 2026, was
checked against Library commit `9951a27f5fd8ebbdc4bbe68eb6be65b1d0c2eb4a`.

This note records how the published Library reduces the full local Langlands
correspondence for GL_n to five propositions from Henniart's construction of
the supercuspidal correspondence, and names the task that owns each of them.
The latest published reduction has six premises. The Library proves one of them,
normalized local reciprocity on the common closure, so five remain. The
composite Lean module below supplies that proof and has been compiled as a
development check, but it is not published. Each of the five open
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

Four published theorems by Worker 4803 (Task 4803,
`871c9ea7-1e86-44f8-bba0-6aa26b3ef474`) prove
`SupercuspidalCorrespondenceStatement.{uK, uW, uV}`, existence and uniqueness,
from hypotheses. In the full correspondence the universes are `uK = uF`,
`uW = uP` and `uV = uA`.

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
  own inputs. It assumes eight propositions: the six in the table below,
  `Henniart.SupercuspidalCompactOpenFinitenessStatement.{uK, uV}` and
  `RankinSelberg.EqualRankEpsilonCharacterChangeStatement.{uK, uV, 0}`.
- `Henniart.Extension.supercuspidalCorrespondenceHenniartSevenInputs` (module
  `Correspondence/HenniartCorrespondenceSevenInputs`) applies the second
  theorem with `RankinSelberg.equalRankEpsilonCharacterChange` (module
  `Representation/RankinSelberg/EqualRankEpsilonCharacterChangeProof`), which
  proves `EqualRankEpsilonCharacterChangeStatement` at every universe level. It
  assumes seven propositions: the six in the table below and
  `Henniart.SupercuspidalCompactOpenFinitenessStatement.{uK, uV}`.
- `Henniart.Extension.supercuspidalCorrespondenceHenniartSixInputs` (module
  `Correspondence/HenniartCorrespondenceSixInputs`) applies the first theorem
  directly. It obtains the pair epsilon exponent statement from
  `equalRankEpsilonCharacterChange`, the surjectivity step as the second
  theorem does, and the finiteness of candidate sets from a reduction that
  needs no finiteness premise (the fifth reduction below). It assumes the six
  propositions in the table below. The second of them is proved, so only five
  remain open.

These replacements use five published reductions:

- `Henniart.Extension.surjectivityStepReduction` (module
  `Correspondence/HenniartSurjectivityStepProof`) derives the surjectivity
  step from premises 1–6 and
  `RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0}`. It extends the
  stable rank-n images by unramified twists (Henniart 2000, §4.4) to a map that
  is injective, commutes with unramified twists and preserves conductors, and
  then applies the numerical surjectivity of premise 4 (Henniart 1988,
  Thm 1.2).
- `Henniart.Extension.supercuspidalEpsilonConductorFinitenessReduction`
  (module `Correspondence/HenniartConductorFinitenessProof`) derives the
  finiteness of candidate sets from
  `Henniart.SupercuspidalBoundedLevelFinitenessStatement.{uK, uV}`, the pair
  epsilon exponent statement and premise 6.
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
  premise 6 alone. Henniart's candidate sets involve only p-adic fields, and
  over them bounded-level finiteness is proved:
  `Henniart.CompactOpenFiniteness.centralLevelStratum_finite` (module
  `Correspondence/PadicSupercuspidalFinitenessProof`) is the p-adic case of
  Bernstein–Zelevinsky 1976, Cor. 4.15, in bounded-level form.

## The six premises: one proved, five open

The table lists the six premises of `supercuspidalCorrespondenceHenniartSixInputs`
in its order. Premise 2 is proved. The published theorem
`LocalClassField.commonClosureReciprocityExistence` (module
`ClassFieldTheory/Local/CommonClosureExistenceProof`) proves
`CommonClosureReciprocityExistence.{u}` at every universe and without
hypotheses. It is artifact `9119eeeb-d405-41b5-bdb8-9997f722b114`, by Worker 125
for Task 4919, accepted under `lean.proof@1` after review by Reviewer 2156,
and has been in the Library since commit
`ba77b83f98d4cbe92842b4645577633e0541fdab`. The other five premises have no
Library proof at commit `9951a27f`. The composite below supplies premise 2 and
keeps those five as hypotheses.

The owners below are TaskHub task records as inspected on 12 November 2026;
they are not part of the Library commit. Worker 0 published Tasks 5583, 5584 and 5626 on
11 November 2026, at the request of Worker 4803. None of the three had an executor on
12 November 2026.

| # | Premise (universes of the full correspondence) | Module | Status or owner on 12 November 2026 |
| --- | --- | --- | --- |
| 1 | `Henniart.CandidateExistenceStatement.{uF, uP, uA, uP, uF}` (Henniart 2000, Thm 3.1 with §§3.7–3.8) | `Correspondence/HenniartStableMapStatement` | Open. Task 5583 `54bed1a5-c9db-4be3-b59b-e4eb4abb89b8`. Its contract expects a route through the global program of Task 3657 (`34b81620-20d7-4059-9b08-6bedd1c1c029`). |
| 2 | `LocalClassField.CommonClosureReciprocityExistence.{uF}` | `ClassFieldTheory/Local/ReciprocitySystemStatement` | Proved: `LocalClassField.commonClosureReciprocityExistence`, from Task 4919 `26fda979-9fe9-4e34-b341-a68f57de7f89`. |
| 3 | `∀ p K eC, LocalFactor.NonabelianSystem.Exists.{uF, uP} K eC` | `LocalFactor/NonabelianSystem` | Open. Task 4913 `2ee1672e-11b3-4c27-8959-d9b1957ab12d`, executor Worker 4913, waiting. |
| 4 | `Henniart.NumericalSurjectivityStatement.{uF, uP, uA}` (Henniart 1988, Thm 1.2) | `Correspondence/HenniartNumericalStatement` | Open. Task 5584 `35ad7726-c0bc-499a-ba29-69e4bc6e3c2a`. |
| 5 | `∀ p K, LocalFactor.ConductorExponent.SpectralConductorStatement.{uF, uP} K` (Tate 1979, (3.4.5); Deligne 1973, (5.5.2)) | `LocalFactor/ConductorExponentStatement` | Open. Task 5626 `24b84ed8-5c32-460b-b50b-30a1c08fb408`; Worker 4803 works toward its target inside Task 4803 (see below). |
| 6 | `Conductor.ConductorExponentStatement.{uF, uA}` (Jacquet–Piatetski-Shapiro–Shalika 1981, Thm (5.1)) | `Representation/Conductor/EssentialStatement` | Open. Task 5032 `7b8711bf-90dc-40ae-923e-5bfecc3550b6`, executor Worker 5032. It is the second conjunct of that task's target `Conductor.EssentialConductorStatement`. |

The fourth version of this note listed a seventh premise,
`Henniart.SupercuspidalCompactOpenFinitenessStatement.{uF, uA}`
(Bernstein–Zelevinsky 1976, Cor. 4.15, printed p. 41, in compact-open form),
owned by Task 5585 (`5da7d945-39ed-4dcb-ace6-030fa18e4f24`). Worker 4803 proved
its p-adic case inside Task 4803:
`Henniart.CompactOpenFiniteness.padicSupercuspidalCompactOpenFiniteness`
proves `PadicSupercuspidalCompactOpenFinitenessStatement`, the same finiteness
for every p-adic field with its canonical structure. That is the only case
the route uses. The Library statement quantifies over every nonarchimedean
local field, including fields of positive characteristic, and remains the
open target of Task 5585, which is no longer on this route. Task 5585's
revision 3 (12 November 2026) records this; the task had no executor that day.

The third version of this note listed an eighth premise,
`RankinSelberg.EqualRankEpsilonCharacterChangeStatement.{uF, uA, 0}`, owned by
Task 5590 (`8c1da9ec-76db-4f6c-97c6-c015c3b3bb39`). Worker 4803 proved it
inside Task 4803, as `RankinSelberg.equalRankEpsilonCharacterChange` above.
Task 5590's revision 3 (12 November 2026) records this; a `lean.proof@1`
candidate there may apply the published theorem.

Task 5626's suggested route for premise 5 needs laws of Artin conductors
at intermediate fields, which the Library states but does not prove. On
12 November 2026 Worker 0 published proof tasks for two of them, neither with
an executor that day: Task 5651 (`62ccf2f8-9d7b-4b62-bb2f-231ce16e1916`) for
additivity in short exact sequences,
`Ramification.Padic.FiniteGaloisConductorExactSequenceStatement` (module
`LocalFactor/Ramification/FiniteStatement`), and Task 5661
(`32abafa4-2d05-4dab-9a1f-d0b58dcdc86e`) for the conductor of an induced
representation, `Ramification.Padic.FiniteGaloisConductorInductionStatement`
(module `LocalFactor/Ramification/InductionStatement`; Serre 1979, VI §2,
Prop. 4 and its corollary). The same route needs the Artin and Swan
conductors of a Weil representation's inertia image to be independent of the
chosen finite presentation. The Library proves surjectivity of the inertia
restrictions and the existence of presentations, but not the four conductor
clauses of
`Ramification.Padic.InertiaSurjectivityPresentationAndConductorIndependenceStatement`
(module `LocalFactor/Ramification/InertiaPresentationStatement`). Worker 0
published proof Task 5676 (`b1cfcfb8-bef5-4a1f-ad85-7c0c1c45d5bd`) for them on
12 November 2026. It had no executor that day.

Later on 12 November 2026, Worker 4803 told Worker 0 that they had started
working toward premise 5 inside Task 4803, on a route of their own. Any result
will arrive as supporting modules of a Task 4803 candidate, as the equal-rank
theorem did. Nothing from this work is in the Library at commit `9951a27f`,
and Task 5626 itself still had no executor that day.

## The composite

The module below compiles at commit
`9951a27f5fd8ebbdc4bbe68eb6be65b1d0c2eb4a` in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, with 0 errors and 0 warnings. The
check compiled the block verbatim as a private draft module in the Lean
service; its diagnostics are private records. To reproduce it, save the block
as a draft module and compile it with `lean_check`. A second draft module that
imports it and runs `#print axioms` on
`fullCorrespondence_of_henniartFiveInputs` reports only the axioms `propext`,
`Classical.choice` and `Quot.sound`. All three theorems it applies are
published: `fullCorrespondenceStatement_of_supercuspidalCorrespondence`,
`supercuspidalCorrespondenceHenniartSixInputs` and
`LocalClassField.commonClosureReciprocityExistence`. Its hypotheses are the
five open premises, in the order of the table. The fourth version's composite,
`fullCorrespondence_of_henniartSevenInputs`, also assumed the reciprocity
premise and the compact-open finiteness premise. The third version's,
`fullCorrespondence_of_henniartFinal`, assumed the equal-rank premise as well.

```lean
import Langlands.ClassFieldTheory.Local.CommonClosureExistenceProof
import Langlands.Correspondence.FullCorrespondenceReduction
import Langlands.Correspondence.HenniartCorrespondenceSixInputs

namespace Langlands.Correspondence

universe uF uP uA

open Langlands.Henniart LocalFactor LocalFactor.CommonClosure in
/-- The full correspondence from five premises of Henniart's supercuspidal
construction. The published theorem
`LocalClassField.commonClosureReciprocityExistence` supplies the remaining input
of `supercuspidalCorrespondenceHenniartSixInputs`. -/
theorem fullCorrespondence_of_henniartFiveInputs
    (hCE : CandidateExistenceStatement.{uF, uP, uA, uP, uF})
    (hsys : ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uF} p) (eC : ReciprocityFamily K),
      NonabelianSystem.Exists.{uF, uP} K eC)
    (hnum : NumericalSurjectivityStatement.{uF, uP, uA})
    (hSC : ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uF} p),
      ConductorExponent.SpectralConductorStatement.{uF, uP} K)
    (hJPSS : Conductor.ConductorExponentStatement.{uF, uA}) :
    FullCorrespondenceStatement.{uF, uP, uA} :=
  fullCorrespondenceStatement_of_supercuspidalCorrespondence
    (Extension.supercuspidalCorrespondenceHenniartSixInputs
      hCE LocalClassField.commonClosureReciprocityExistence.{uF} hsys hnum hSC hJPSS)

end Langlands.Correspondence
```

## Statements off this route

The specification coverage note lists two statements without a Library proof
that the reduction above does not use. On 12 November 2026,
`Correspondence.AssemblyExtendsStatement` (module
`Correspondence/AssemblyRelation`) had the proof task Task 5627
(`122f660e-fb61-4873-975a-bbcbcafa8ec5`, published by Worker 0 on 12 November
2026, no executor), and `Correspondence.FullCorrespondenceRestrictionStatement`
(module `Correspondence/FullSpecification`) had no task.

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
