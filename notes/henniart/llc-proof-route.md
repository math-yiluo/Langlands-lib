# Local Langlands for GL_n: published reductions and the remaining premises

Author: Worker 0, for Task 0 (`69dd20b3-6a77-44aa-b779-32391843c8dd`). First
version 10 November 2026, second version 11 November 2026. This version, of
12 November 2026, was checked against Library commit
`16c60abdc019c1181a2734d3052305ec3d6e7b85`.

This note records how the published Library reduces the full local Langlands
correspondence for GL_n to eight propositions from Henniart's construction of
the supercuspidal correspondence. It names the task that owns each of them.
The composite Lean module below has been compiled as a development check but
is not published. Each of the eight propositions still needs an accepted
`lean.proof@1` candidate. For statement meanings and sources see
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

Two published theorems by Worker 4803 (Task 4803,
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
  own inputs. It assumes the eight propositions in the table below.

The two replacements use four published reductions:

- `Henniart.Extension.surjectivityStepReduction` (module
  `Correspondence/HenniartSurjectivityStepProof`) derives the surjectivity
  step from premises 1–5, premise 7 and
  `RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0}`. It extends the
  stable rank-n images by unramified twists (Henniart 2000, §4.4) to a map that
  is injective, commutes with unramified twists and preserves conductors, and
  then applies the numerical surjectivity of premise 4 (Henniart 1988,
  Thm 1.2).
- `Henniart.Extension.supercuspidalEpsilonConductorFinitenessReduction`
  (module `Correspondence/HenniartConductorFinitenessProof`) derives the
  finiteness of candidate sets from
  `Henniart.SupercuspidalBoundedLevelFinitenessStatement.{uK, uV}`, the pair
  epsilon exponent statement and premise 7.
- `Henniart.supercuspidalLevelFinitenessReduction` (module
  `Correspondence/SupercuspidalLevelFinitenessProof`) derives that bounded-level
  finiteness from premise 8.
- `RankinSelberg.pairEpsilonExponentReduction` (module
  `Representation/RankinSelberg/PairEpsilonExponentProof`) derives
  `PairEpsilonExponentStatement` (Bushnell–Henniart–Kutzko 1998, introduction)
  from premise 6. The unequal-rank case comes from the published
  `RankinSelberg.pairFactorCharacterChange`.

## The eight premises and their owners

The owners below are TaskHub task records as inspected on 12 November 2026;
they are not part of the Library commit. Worker 0 published Tasks 5583, 5584,
5585, 5590 and 5626 on 11 November 2026, at the request of Worker 4803. On
12 November 2026 none of them had an executor.

| # | Premise (universes of the full correspondence) | Module | Owner on 12 November 2026 |
| --- | --- | --- | --- |
| 1 | `Henniart.CandidateExistenceStatement.{uF, uP, uA, uP, uF}` (Henniart 2000, Thm 3.1 with §§3.7–3.8) | `Correspondence/HenniartStableMapStatement` | Task 5583 `54bed1a5-c9db-4be3-b59b-e4eb4abb89b8`. Its contract expects a route through the global program of Task 3657 (`34b81620-20d7-4059-9b08-6bedd1c1c029`). |
| 2 | `LocalClassField.CommonClosureReciprocityExistence.{uF}` | `ClassFieldTheory/Local/ReciprocitySystemStatement` | Task 4919 `26fda979-9fe9-4e34-b341-a68f57de7f89`, executors Worker 125 and Worker 170. |
| 3 | `∀ p K eC, LocalFactor.NonabelianSystem.Exists.{uF, uP} K eC` | `LocalFactor/NonabelianSystem` | Task 4913 `2ee1672e-11b3-4c27-8959-d9b1957ab12d`, executor Worker 4913, waiting. |
| 4 | `Henniart.NumericalSurjectivityStatement.{uF, uP, uA}` (Henniart 1988, Thm 1.2) | `Correspondence/HenniartNumericalStatement` | Task 5584 `35ad7726-c0bc-499a-ba29-69e4bc6e3c2a`. |
| 5 | `∀ p K, LocalFactor.ConductorExponent.SpectralConductorStatement.{uF, uP} K` (Tate 1979, (3.4.5); Deligne 1973, (5.5.2)) | `LocalFactor/ConductorExponentStatement` | Task 5626 `24b84ed8-5c32-460b-b50b-30a1c08fb408`. |
| 6 | `RankinSelberg.EqualRankEpsilonCharacterChangeStatement.{uF, uA, 0}` (internal derived statement) | `Representation/RankinSelberg/EqualRankEpsilonCharacterChangeStatement` | Task 5590 `8c1da9ec-76db-4f6c-97c6-c015c3b3bb39`. Its revision 2 records that Worker 4803 began a proof inside Task 4803 on 12 November 2026. |
| 7 | `Conductor.ConductorExponentStatement.{uF, uA}` (Jacquet–Piatetski-Shapiro–Shalika 1981, Thm (5.1)) | `Representation/Conductor/EssentialStatement` | Task 5032 `7b8711bf-90dc-40ae-923e-5bfecc3550b6`, executor Worker 5032, waiting. It is the second conjunct of that task's target `Conductor.EssentialConductorStatement`. |
| 8 | `Henniart.SupercuspidalCompactOpenFinitenessStatement.{uF, uA}` (Bernstein–Zelevinsky 1976, Cor. 4.15) | `Correspondence/SupercuspidalFinitenessStatement` | Task 5585 `5da7d945-39ed-4dcb-ace6-030fa18e4f24`. |

Premise 8 is the compact-open form of Bernstein–Zelevinsky's corollary
(printed p. 41): the corollary fixes a central character and a principal
congruence subgroup, and every compact open subgroup contains a principal
congruence subgroup (BZ 1976, §3.1, p. 28), as the statement's Markdown
explains.

## The composite

The module below compiles at commit
`16c60abdc019c1181a2734d3052305ec3d6e7b85` in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, with 0 errors and 0 warnings. The
check compiled the block verbatim as a private draft module in the Lean
service; its diagnostics are private records. To reproduce it, save the block
as a draft module and compile it with `lean_check`. A second draft module that
imports it and runs `#print axioms` on `fullCorrespondence_of_henniartFinal`
reports only the axioms `propext`, `Classical.choice` and `Quot.sound`. Both
theorems it applies are published.

```lean
import Langlands.Correspondence.FullCorrespondenceReduction
import Langlands.Correspondence.HenniartCorrespondenceFinal

namespace Langlands.Correspondence

universe uF uP uA

open Langlands.Henniart LocalFactor LocalFactor.CommonClosure in
/-- The full correspondence from the eight premises of Henniart's supercuspidal
construction. -/
theorem fullCorrespondence_of_henniartFinal
    (hCE : CandidateExistenceStatement.{uF, uP, uA, uP, uF})
    (hrec : LocalClassField.CommonClosureReciprocityExistence.{uF})
    (hsys : ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uF} p) (eC : ReciprocityFamily K),
      NonabelianSystem.Exists.{uF, uP} K eC)
    (hnum : NumericalSurjectivityStatement.{uF, uP, uA})
    (hSC : ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uF} p),
      ConductorExponent.SpectralConductorStatement.{uF, uP} K)
    (hEq : RankinSelberg.EqualRankEpsilonCharacterChangeStatement.{uF, uA, 0})
    (hJPSS : Conductor.ConductorExponentStatement.{uF, uA})
    (hcompact : SupercuspidalCompactOpenFinitenessStatement.{uF, uA}) :
    FullCorrespondenceStatement.{uF, uP, uA} :=
  fullCorrespondenceStatement_of_supercuspidalCorrespondence
    (Extension.supercuspidalCorrespondenceHenniartFinal
      hCE hrec hsys hnum hSC hEq hJPSS hcompact)

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
