# Local Langlands for GL_n: published reductions and the remaining premises

Author: Worker 0, for Task 0 (`69dd20b3-6a77-44aa-b779-32391843c8dd`). First
version 10 November 2026. This version, of 11 November 2026, was checked against
Library commit `f7cf04f0523631a4ffd94d4443c142d27505965e`.

This note records how the published Library reduces the full local Langlands
correspondence for GL_n to five propositions from Henniart's construction of
the supercuspidal correspondence. It names the open inputs below those five
propositions and the tasks that own them. The composite Lean module below has
been compiled as a development check but is not published. Each open
proposition still needs an accepted `lean.proof@1` candidate. For statement
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
by Lean name. The first version of this note listed seven open inputs; the six
other than supercuspidal existence now have published proofs. Task 4806's
published `Correspondence.fullCharacterization`
(`Correspondence/FullCharacterizationProof`) proves Henniart 2002, Cor. 1.8, on
its own as well.

## Published: Henniart's construction with the rank induction

The published theorem
`Henniart.Extension.supercuspidalCorrespondenceHenniartInduction` (module
`Correspondence/HenniartCorrespondenceInduction`, by Worker 4803) proves
`SupercuspidalCorrespondenceStatement.{uK, uW, uV}` from five propositions, each
a published Library statement. In the full correspondence the universes are
`uK = uF`, `uW = uP` and `uV = uA`. It carries out Henniart's induction on the
rank (Henniart 2000, §4.3) with the published proofs of the rank-one stage
(`Correspondence/HenniartRankOneStageProof`) and of the inductive step
(`Correspondence/HenniartChoiceIndependenceStepProof`). Its conclusion includes
uniqueness.

The owners below are TaskHub task records as inspected on 11 November 2026;
they are not part of the Library commit. Tasks 5583, 5584, 5585 and 5590 were
published by Worker 0 on 11 November 2026, at the request of Worker 4803, and
had no executor yet.

| # | Premise | Module | Owner on 11 November 2026 |
| --- | --- | --- | --- |
| 1 | `Henniart.CandidateExistenceStatement.{uF, uP, uA, uP, uF}` (Henniart 2000, Thm 3.1 with §§3.7–3.8) | `Correspondence/HenniartStableMapStatement` | Task 5583 `54bed1a5-c9db-4be3-b59b-e4eb4abb89b8`. Its contract expects a route through the global program of Task 3657 (`34b81620-20d7-4059-9b08-6bedd1c1c029`). |
| 2 | `Henniart.SurjectivityStepStatement.{uF, uP, uA, uP}` (Henniart 2000, §4.3, citing Henniart 1988) | same | Task 4803 (`871c9ea7-1e86-44f8-bba0-6aa26b3ef474`, executor Worker 4803). Its deep input, `Henniart.NumericalSurjectivityStatement` (Henniart 1988, Thm 1.2; module `Correspondence/HenniartNumericalStatement`), is Task 5584 `35ad7726-c0bc-499a-ba29-69e4bc6e3c2a`. |
| 3 | `Henniart.SupercuspidalEpsilonConductorFinitenessStatement.{uF, uA}` (Henniart 2000, §4.3, the finite set `P`) | same | Task 4803; see the next section. |
| 4 | `LocalClassField.CommonClosureReciprocityExistence.{uF}` | `ClassFieldTheory/Local/ReciprocitySystemStatement` | Task 4919 `26fda979-9fe9-4e34-b341-a68f57de7f89`, executors Worker 125 and Worker 170. |
| 5 | `∀ p K eC, LocalFactor.NonabelianSystem.Exists.{uF, uP} K eC` | `LocalFactor/NonabelianSystem` | Task 4913 `2ee1672e-11b3-4c27-8959-d9b1957ab12d`, executor Worker 4913, waiting. |

Task 5584's contract records the plan for premise 2: Worker 4803 is to derive
it inside Task 4803 from numerical surjectivity. The stable map, extended by
unramified twists (Henniart 2000, §4.4), is injective, commutes with
unramified twists and preserves conductors.

## The conductor-finiteness branch

Task 4803's candidate `2e8d0b64-1a0d-4a48-a736-e49df431bf89` was staged for
review on 11 November 2026; it is not in the Library. Its statement says that
premise 3 at `.{uK, uV}` follows from three published statements:

- `Henniart.SupercuspidalBoundedLevelFinitenessStatement.{uK, uV}`: finitely
  many supercuspidal classes with a fixed central character and bounded
  newvector level, the first level with a nonzero vector fixed by the last-row
  congruence subgroup of Jacquet–Piatetski-Shapiro–Shalika 1981, §5.1. The
  published `Henniart.supercuspidalLevelFinitenessReduction`
  (`Correspondence/SupercuspidalLevelFinitenessProof`) derives it from
  `Henniart.SupercuspidalCompactOpenFinitenessStatement`
  (`Correspondence/SupercuspidalFinitenessStatement`), which is Task 5585
  `5da7d945-39ed-4dcb-ace6-030fa18e4f24`. That statement is the compact-open
  form of Bernstein–Zelevinsky 1976, Cor. 4.15 (printed p. 41): the corollary
  fixes a central character and a principal congruence subgroup, and every
  compact open subgroup contains a principal congruence subgroup (BZ 1976,
  §3.1, p. 28), as the statement's Markdown explains.
- `RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0}`
  (Bushnell–Henniart–Kutzko 1998, introduction;
  `Representation/RankinSelberg/PairEpsilonNormalizationStatement`). Task 4803's
  candidate `c2221724-b7f3-46f3-bd18-af857ba70ba2`, staged on 11 November 2026,
  states that `RankinSelberg.EqualRankEpsilonCharacterChangeStatement` implies it
  at the same universes. The unequal-rank case comes from the published
  `RankinSelberg.pairFactorCharacterChange`
  (`Representation/RankinSelberg/PairFactorCharacterChangeProof`), whose second
  component is `UnequalRankEpsilonCharacterChangeStatement`. The equal-rank
  statement (`Representation/RankinSelberg/EqualRankEpsilonCharacterChangeStatement`,
  an internal derived statement) is Task 5590
  `8c1da9ec-76db-4f6c-97c6-c015c3b3bb39`.
- `Conductor.ConductorExponentStatement.{uK, uV}` (Jacquet–Piatetski-Shapiro–Shalika
  1981, Thm 5.1; `Representation/Conductor/EssentialStatement`). It is the
  second conjunct of `Conductor.EssentialConductorStatement`, the target of
  Task 5032 `7b8711bf-90dc-40ae-923e-5bfecc3550b6` (executor Worker 5032,
  waiting).

## The composite

The module below compiles at commit `f7cf04f0` in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, with 0 errors and 0 warnings. The
check compiled the block verbatim as a private draft module in the Lean
service; its diagnostics are private records. To reproduce it, save the block
as a draft module and compile it with `lean_check`. A second draft module that
imports it and runs `#print axioms` on
`fullCorrespondence_of_henniartInduction` reports only the axioms `propext`,
`Classical.choice` and `Quot.sound`. Both theorems it applies are published.

```lean
import Langlands.Correspondence.FullCorrespondenceReduction
import Langlands.Correspondence.HenniartCorrespondenceInduction

namespace Langlands.Correspondence

universe uF uP uA

open Langlands.Henniart LocalFactor.CommonClosure in
/-- The full correspondence from the five premises of Henniart's supercuspidal
construction with the rank induction carried out. -/
theorem fullCorrespondence_of_henniartInduction
    (hCE : CandidateExistenceStatement.{uF, uP, uA, uP, uF})
    (hsurj : SurjectivityStepStatement.{uF, uP, uA, uP})
    (hfin : SupercuspidalEpsilonConductorFinitenessStatement.{uF, uA})
    (hrec : LocalClassField.CommonClosureReciprocityExistence.{uF})
    (hsys : ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uF} p) (eC : ReciprocityFamily K),
      LocalFactor.NonabelianSystem.Exists.{uF, uP} K eC) :
    FullCorrespondenceStatement.{uF, uP, uA} :=
  fullCorrespondenceStatement_of_supercuspidalCorrespondence
    (Extension.supercuspidalCorrespondenceHenniartInduction hCE hsurj hfin hrec hsys)

end Langlands.Correspondence
```

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
