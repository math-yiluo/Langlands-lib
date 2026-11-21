# Harris 1998 Proposition 4.8 under the exact-stabilizer condition: statements, reduction and proof ownership

Status pin: Library commit `d8ac05cfe4cf72b832a220bfc3374d807ef9424b` and
TaskHub records of 21 November 2026. (Its Lean files are the same as those of
`b47a2385d86db05fb5e69eda98e948bf2539ada2`.) This note is the map for Task 7343
(`d6ca8ef3-60ca-4650-a436-8b5a00655394`), which the operator published. That
task restates Harris 1998, Proposition 4.8, and its induction with Harris's
condition (4.12) on the auxiliary character
(`Langlands.Global.GeneralPosition.HasExactWeilStabilizer`) in place of
general position. It
also states the interfaces B5, B6 and B7 of the operator's plan note (source
`operator-external-inputs-plan-2026-11-16`, Section 2.2, Section 4.8 with
Remark 4.2).

Task 7343 published no mathematics of its own. Its child tasks published the
new statements and definitions of the first table; the "Stated by" column
names the child. In that table, only the general form of III.4.2(c) is an
existing Library statement that no child stated. The reduction also reuses
existing Library statements of the general-position formulation, which no
child of Task 7343 stated: the auxiliary parity inputs, the Mackey step, A1,
C2, isobaric invariance and the old transfer inputs B1–B4 (positions 2, 3, 5
and 11–17 of the second table), and the general III.4.2(c) (position 20).
The proof column of each table names the task that owns the proof; not all
of these tasks are children of Task 7343. The general-position
formulation is in the [Proposition 4.8 route](proposition-48-route.md). That
formulation, its child tasks and the Drinfeld-tower proof of the comparison A2
stay open as the fallback. None of them was retired, revised or weakened. The
published theorem `proposition48ExactStabilizerStatement_of_proposition48Statement`
shows that the general-position form implies the exact-stabilizer form.

Lean names given without a namespace are in `Langlands.Global.Harris` (modules
under `Langlands/Global/Arithmetic/`) or in `Langlands.Automorphic.Unramified`
(modules under `Langlands/Automorphic/Unramified/`). Names in other
namespaces are always written in full: A1 and A2 are in
`Langlands.GaloisRepresentation` (modules under `Langlands/Galois/`), the bridge
is in `Langlands.Automorphic`, the σ-lift predicate is in
`Langlands.BaseChange`, and the consumers are in `Langlands.Global` or
`Langlands.Henniart`. "TC" means the totally complex form. The
"Declarations" column of the first table gives the module of each TC form.

## Design decisions

- **B6 as stated.** The executors chose B6 as stated in the plan note,
  Section 2.2, not the variant in Remark 4.2. The choice and its reason are
  recorded in the contexts of the first two child tasks: Task 7413
  (`afd2318f-b1bd-4392-85ce-2b4278cc4a47`) and Task 7417
  (`825a18d4-056a-4fe0-9099-4e07aa786efe`). The reason is that the published
  branch hypotheses give solutions for the immediate Mackey children only,
  while the variant needs solutions along a whole tower. In return, the
  planned derivation of B6 needs the general III.5.1 premise described below,
  not only a restricted form of III.5.1.
- **Operator rulings.** Their files are in the shared correspondence
  directory.
  - `89b70579f7465ae3994e304e80cf284b`: B7 is stated literally, and the
    archimedean bridge is a separate named premise.
  - `afc4eb775dc157d6807bbc17caa2b02b`: B6 and B7 are canonical statements
    with no E2 or III.5.1 hypothesis inside them. Arthur–Clozel III.5.1 in
    the generality of the source becomes its own named, unproved premise.
    The branches use B6 only through the distinctness lemma (claim (2) of
    Remark 4.2), and B7 only in a restricted form.
  - `a79e2e832569567a8582b3c994f2fc1b` (R2): solutions of the restated
    induction carry their complex-place parameters.
  - `c05e16c66b7657e9aca53372f4114a52`: B5r is stated beside B5. The singleton
    branch uses B5r, with the conjugate place as the second finite place.
    Canonical B5 stays published and is not used by the branches.
- **The general III.5.1 premise.** Task 7889 stated it as
  `CyclicStrongBaseChangeSupportStatement`. This declaration is the
  support-and-parameter consequence of Arthur–Clozel III.5.1 for general
  unitary isobaric data, not a transcription of III.5.1 (see its
  [Markdown](../../Langlands/Automorphic/Unramified/CyclicStrongBaseChangeSupportStatement.md)).
  It has no CM, totally complex, regular-algebraic or supercuspidal
  hypothesis on the global data. It has four clauses. At a nonsplit finite
  place with a unique place above it, it takes a local map that is certified
  by σ-lift character identities
  (`Langlands.BaseChange.IsSigmaLiftOnSupercuspidals` for every
  `σ ≠ 1`) and an arbitrary witness of the downstairs supercuspidal support.
  It concludes that the image of that witness under the map is an upstairs
  support. It asserts neither the existence of a certified map nor that of a
  downstairs support. The other three clauses transport supports at split
  finite places and parameter lists at complex and real places. The
  real-to-real clause holds only for lists whose induced blocks have nonzero
  weight.
- **General and restricted proof programs.** Under ruling `afc4eb77` (items
  3 and 4) and ruling `c05e16c6` (item 4), canonical B5, B6 and B7 rest on
  the general premise. Task 7340 delivers them only as conditional
  derivations from it. The general premise is beyond the simple trace
  formula; the restricted forms are not. So the restricted route stays the
  intended end. The branches use B5r, the restricted B7 and the
  distinctness lemma, and the general premise enters them only through B6
  in that lemma. The restricted III.5.1 of Task 7465
  (`RestrictedCyclicBaseChangeCompatibilityStatement`) is a separate
  statement, not the premise of Task 7889. The whole-tower variant of B6 is
  to be decided once that restricted III.5.1 is proved (ruling `afc4eb77`,
  item 5).

## Statements and their proof owners

| Item | Declarations (module) | Stated by | Proof |
| --- | --- | --- | --- |
| B5 | `CyclicWeakBaseChangeSupercuspidalStatement` and TC `CyclicWeakBaseChangeSupercuspidalTCStatement` (both in `CyclicWeakBaseChangeSupercuspidalStatement`) | Task 7425 | Task 7340 (open): only a conditional derivation from the general III.5.1 premise at `v` with E2, after B5r (ruling `c05e16c6`, item 4) |
| B5r | `RestrictedCyclicWeakBaseChangeSupercuspidalStatement` and TC `RestrictedCyclicWeakBaseChangeSupercuspidalTCStatement` (both in `RestrictedCyclicWeakBaseChangeSupercuspidalStatement`) | Task 7897 | Task 7340 (open), by the twisted simple trace formula. The proof names E2 (local descent of σ-stable supercuspidal classes) and the fibre statement (Arthur–Clozel III.3.1) as inputs (ruling `c05e16c6`, item 3) |
| B6 | `TowerBaseChangeHeckeComponentStatement` and TC `TowerBaseChangeHeckeComponentTCStatement` (both in `TowerBaseChangeHeckeComponentStatement`); vocabulary `PrimeCyclicBaseChangeTower` | Tasks 7478, 7417 | Task 7340 (open): a conditional derivation from the general III.5.1 premise with E2 and Arthur–Clozel I.6 (ruling `afc4eb77`, item 3) |
| III.4.2(c) | general `CyclicPrimeIsobaricBaseChangeStatement` (module `IsobaricCyclicTransferStatement`, published earlier); TC `CyclicPrimeIsobaricBaseChangeTCStatement` (its own module `CyclicPrimeIsobaricBaseChangeTCStatement`, Task 7478) | see column 2 | general form: unproved external input, Arthur–Clozel III Thm 4.2(c), p. 202; TC form: Task 7860 `835f1bf4-f1d3-4a52-ac52-54475877d275` (open) |
| III.5.1 (general premise) | `CyclicStrongBaseChangeSupportStatement` (one form only): the support-and-parameter consequence of Arthur–Clozel III.5.1 for general unitary isobaric data ([Markdown](../../Langlands/Automorphic/Unramified/CyclicStrongBaseChangeSupportStatement.md)). Its nonsplit clause takes a σ-lift-certified local map and a downstairs support witness | Task 7889 | unproved external input (ruling `afc4eb77`, item 2). It is not the restricted III.5.1 of Task 7465 |
| B7 | `CyclicWeakBaseChangeComplexPlaceStatement` and TC `CyclicWeakBaseChangeComplexPlaceTCStatement` (both in `CyclicWeakBaseChangeComplexPlaceStatement`); vocabulary from Tasks 7435 and 7466 | Task 7479 | Task 7340 (open): a conditional derivation from the general III.5.1 premise at the complex places (ruling `afc4eb77`, item 3). Not used by the branches |
| restricted B7 | `RestrictedCyclicWeakBaseChangeComplexPlaceStatement` (one form only) | Task 7552 | Task 7340 (open) |
| bridge | `Langlands.Automorphic.CuspidalComplexParameterBridgeTCStatement` (TC form only, module `Automorphic/CuspidalComplexParameterBridgeStatement`); vocabulary from Task 7455 | Task 7463 | proved: `Langlands.Automorphic.cuspidalComplexParameterBridgeTC` (`Automorphic/CuspidalComplexParameterBridgeProof`, Task 7870) |
| datum and validity | `IsProposition48ExactStabilizerDatum`, `Proposition48Problem.{IsExactStabilizerValid, IsExactStabilizerValidAtParity, IsAuxiliaryExactStabilizerValidAtParity, IsAuxiliaryExactStabilizerValid}` with forgetful lemmas (`HarrisProposition48ExactStabilizerData`) | Task 7413 | definitions |
| restated proposition | `Proposition48ExactStabilizerStatement` (`HarrisProposition48ExactStabilizerStatement`) | Task 7413 | Task 8181 (open) |
| inheritance | `Proposition48ExactStabilizer{Mackey,Parity}InheritanceStatement` (`HarrisProposition48ExactStabilizerInheritanceStatement`) | Task 7413 | proved: `proposition48ExactStabilizerMackeyInheritance`, `proposition48ExactStabilizerParityInheritance` (Tasks 7631, 7630) |
| parameter data | `Proposition48Problem.{IsInducedComplexPlaceParameter, HasInducedComplexPlaceParameters, HasParameterSolution, IsMackeyConstituent, HasDistinctMackeyComponents}` (`HarrisProposition48ExactStabilizerParameterData`) | Task 7563 | definitions |
| rank one, untwist | `Proposition48ExactStabilizerAuxiliaryRankOneStatement`, `Proposition48ExactStabilizerParameterUntwistStatement` (`HarrisProposition48ExactStabilizerParameterAuxiliaryStatement`) | Task 7563 | proved: `proposition48ExactStabilizerAuxiliaryRankOne`, `proposition48ExactStabilizerParameterUntwist` (Task 7783) |
| distinctness | `Proposition48ExactStabilizerDistinctnessStatement` and TC `...DistinctnessTCStatement` (both in `HarrisProposition48ExactStabilizerDistinctnessStatement`) | Task 7563 | proved: `proposition48ExactStabilizerDistinctness`, `proposition48ExactStabilizerDistinctnessTC` (Task 7784) |
| prime branch | `Proposition48ExactStabilizerPrimeBranchStatement` and TC `...PrimeBranchTCStatement` (both in `HarrisProposition48ExactStabilizerBranchStatement`) | Task 7563 | Task 7785 completed its decomposition. Its reduction statement (Task 7825) is published; the open proofs are the reduction, Task 8182 `7fbaf0ff-5180-47ee-859a-e3140c57cfff`, and the exact assembly, Task 8183 `d6261458-f2bc-4bc2-99de-a661d18fccd6` |
| singleton branch | `Proposition48ExactStabilizerSingletonBranchStatement` and TC `...SingletonBranchTCStatement` (both in `HarrisProposition48ExactStabilizerBranchStatement`) | Task 7563 | Task 7786 revision 2 (open), as a corollary of the restricted branch: B5 implies B5r |
| restricted singleton branch | `Proposition48ExactStabilizerRestrictedSingletonBranchStatement` and TC `...RestrictedSingletonBranchTCStatement` (both in `HarrisProposition48ExactStabilizerRestrictedDescentStatement`) | Task 7897 | Task 7786 revision 2 (open); its reduction statement is Task 8232 (open) |
| reduction | `Proposition48ExactStabilizerReductionStatement` and TC `...ReductionTCStatement` (both in `HarrisProposition48ExactStabilizerReductionStatement`) | Task 7563 | Task 8180 (open), as a corollary of the restricted reduction |
| restricted reduction | `Proposition48ExactStabilizerRestrictedReductionStatement` and TC `...RestrictedReductionTCStatement` (both in `HarrisProposition48ExactStabilizerRestrictedDescentStatement`) | Task 7897 | Task 8180 (open) |

In the restated branches, B6 does not appear directly. It enters the prime
branch through the hypothesis
`Proposition48Problem.HasDistinctMackeyComponents`, which the
distinctness statement derives from B6, III.4.2(c) and spectral rigidity.
This replaces the premise A2
(`Langlands.GaloisRepresentation.HarrisSupercuspidalLocalComparisonStatement`,
module `Langlands/Galois/HarrisSupercuspidalLocalComparisonStatement`).
The published singleton branch takes B5 as a premise; the restricted singleton
branch takes B5r in its place. Both branches take the restricted B7 and the
bridge. The canonical B7 is a published statement that the branches do not
use.

**The active singleton route.** Task 7786 revision 2 proves the restricted
singleton branch first. In the Mackey case with one double coset, the branch
applies TC B5r to every weak descent, in both orders, at the auxiliary
conjugate pair: `v = Q.Ps.v` and the second finite place
`v' = conjPlace Q.E Q.Ps.v`. The two places differ because `p` splits in `K₀`
(the named input `SplitPlaceNeConjPlaceStatement`). The validity clauses of the
problem give unique places of `Q.L` above both, hence unique places of the
prime cyclic step `D` above both. One cuspidal presentation of the lift is
supercuspidal at both places. Task 8232
(`27bdeee6-2af1-49d6-9d33-5cecec9501b8`, open) is to state this reduction of
the TC restricted branch to thirteen named inputs. The published singleton branch and
its TC form then follow from the restricted ones, because B5 implies B5r.
Canonical B5 is not put into the restricted branch proof.

## The named inputs of the reduction

`Proposition48ExactStabilizerReductionStatement.{uF, uV}` derives
`Proposition48ExactStabilizerStatement.{uF, 0, 0, 0, uV}` from the 22
conjuncts below, in this order. Its Markdown gives the exact universes and the
sources. `Proposition48ExactStabilizerRestrictedReductionStatement.{uF, uV}`
has the same conjuncts and conclusion, except at positions 10 and 18, where the
table gives the replacement after "restricted:". The TC forms of both reductions
use the TC forms at positions 8–10 and 12–20 and the same declarations at
positions 1–7, 11, 21 and 22.

| Pos. | Declaration | Source | Proof status or owner |
| --- | --- | --- | --- |
| 1 | `Proposition48ExactStabilizerAuxiliaryRankOneStatement` | internal (R2) | proved (Task 7783) |
| 2 | `Proposition48AuxiliaryParityNormalizationStatement` | general-position input | Task 8008 (decomposition: Task 7218) |
| 3 | `Proposition48AuxiliaryParityUntwistStatement` | general-position input | Task 8009 (decomposition: Task 7218) |
| 4 | `Proposition48ExactStabilizerParameterUntwistStatement` | internal (R2) | proved (Task 7783) |
| 5 | `Proposition48MackeyStepStatement` | general-position input | proved: `proposition48MackeyStep` (Task 7219) |
| 6 | `Proposition48ExactStabilizerMackeyInheritanceStatement` | plan note Section 4.8 | proved (Task 7631) |
| 7 | `Proposition48ExactStabilizerParityInheritanceStatement` | plan note Section 4.8 | proved (Task 7630) |
| 8 | `Proposition48ExactStabilizerDistinctnessStatement` | plan note Remark 4.2 (2) | proved (Task 7784) |
| 9 | `Proposition48ExactStabilizerPrimeBranchStatement` | Harris pp. 201–203 | Task 8183 (decomposition: Task 7785) |
| 10 | `Proposition48ExactStabilizerSingletonBranchStatement`; restricted: `Proposition48ExactStabilizerRestrictedSingletonBranchStatement` | Harris pp. 201–203 | Task 7786 (both) |
| 11 | `Langlands.GaloisRepresentation.Harris1998Theorem12CuspidalStatement` (A1; module `Langlands/Galois/Harris1998ExistenceStatement`) | general-position input (Harris Thm 1.2) | Task 7874 `a2d0f23a-d026-467f-998d-8e1b9cd12b4d` (exact proof assembly); Task 6698 is the planning program |
| 12 | `CuspidalSpectralRigidityStatement` (C2) | general-position input | Task 6446, revision 2 |
| 13 | `Proposition48IsobaricInvarianceStatement` | general-position input | proved: `proposition48IsobaricInvariance`, TC `proposition48IsobaricInvarianceTC` (Task 7220) |
| 14 | `CyclicRegularInductionStatement` (B2) | general-position input | Task 6699, revision 2 |
| 15 | `CyclicRegularOrbitLiftStatement` (B3) | general-position input | Task 6699, revision 2 |
| 16 | `CyclicStableDescentStatement` (B1) | general-position input | Task 6699, revision 2 |
| 17 | `CyclicWeakInductionSupercuspidalStatement` (B4) | general-position input | Task 6845, revision 2 |
| 18 | `CyclicWeakBaseChangeSupercuspidalStatement` (B5); restricted: `RestrictedCyclicWeakBaseChangeSupercuspidalStatement` (B5r) | plan note Section 2.2; ruling `c05e16c6` | Task 7340 (both; see the first table) |
| 19 | `TowerBaseChangeHeckeComponentStatement` (B6) | plan note Section 2.2 | Task 7340, conditional on the general III.5.1 premise |
| 20 | `CyclicPrimeIsobaricBaseChangeStatement` (III.4.2(c)) | Arthur–Clozel III Thm 4.2(c) | general form unproved; TC form Task 7860 |
| 21 | `RestrictedCyclicWeakBaseChangeComplexPlaceStatement` (restricted B7) | plan note Section 2.2, ruling `afc4eb77` | Task 7340 |
| 22 | `Langlands.Automorphic.CuspidalComplexParameterBridgeTCStatement` (bridge) | ruling `89b70579` | proved: `Langlands.Automorphic.cuspidalComplexParameterBridgeTC` |

Positions 2, 3, 5 and 11–17, and the general form at position 20, are
existing Library statements reused from the general-position formulation. No
child of Task 7343 stated them. Their owners are those of the
[Proposition 4.8 route](proposition-48-route.md), except that Task 7874 now
owns the exact proof of A1 and Tasks 8008 and 8009 own the exact proofs at
positions 2 and 3. Compared with `Proposition48ReductionStatement`, the
reduction drops A2 and replaces the rank-one input and the two branches. It adds
positions 4, 6–8 and 18–22.

## Carry-over of the open children of the general-position formulation

| Task | Target | For the exact-stabilizer route |
| --- | --- | --- |
| 7218 `8a1e00f3-5223-4c5a-9994-f8f08331ceda` | parity normalization and untwist | carries over unchanged (positions 2, 3) |
| 7219 `03216936-611f-40ff-9fbf-4aca7b6cec03` | Mackey step | carries over unchanged (position 5) |
| 7220 `549b134f-cd9d-42ad-94bc-2d2ff16386c1` | isobaric invariance, with TC | carries over unchanged (position 13) |
| 7216 `22c6a336-836c-47dc-bc09-667768393b20` | rank one | second version: the parameter form, Task 7783 `bb8260ea-d6a2-457a-95f1-e5ed5dfe5823` (proved) |
| 7221 `528311c0-f3fd-4553-ad48-a6bed4282b5a` | prime branch | second version: Task 7785 `2cdbece0-e746-4cbc-8ecb-0cc9273a8a76` (decomposition completed; exact assembly Task 8183) |
| 7222 `95f79351-962f-4e98-a877-d3ca1aa759e1` | singleton branch | second version: Task 7786 `794a4691-1e86-44f4-a28d-d79270146b71`, revision 2 |
| 7213 `b517f901-0ac4-4ae4-a08e-b8b88a3b0fec` | reduction proof | second version: Task 8180 `ef87ecab-644c-4a4e-9861-ac68f6037d2e`; it reuses the helpers of the published `proposition48Reduction` |
| 6702 `0aa2189a-e878-4144-9d41-b76799d87cfc` | final assembly | second version: Task 8181 `ed256098-04c9-409e-988d-9920b92dcf82` |

None of the eight tasks is inapplicable. The proof program of A2, Task 6846,
is not on this list. It is not needed by the exact-stabilizer route and stays
open as the fallback. Every first version keeps its original target.

## Consumers

Task 7627 (`2e02289a-da25-4f0f-a8a1-e40f7c12db94`) stated Henniart's uses of
the restated proposition. Task 7751 proved the datum statement and the two
reductions over a general base, and Task 7752 proved the TC reduction.

- `Langlands.Global.HarrisDatumCharacterRealizationExactStabilizerStatement`:
  proved by `Langlands.Global.harrisDatumCharacterRealizationExactStabilizer`.
  It supplies Henniart's datum characters with the exact Weil stabilizer.
- `Langlands.Global.HenniartGlobalizationExactStabilizerStatement`: the
  restated proposition implies `Langlands.Global.RelativeGaloisGlobalization`
  (Task 5134 with the restated proposition). It is unproved. Its reduction
  `Langlands.Global.HenniartGlobalizationExactStabilizerReductionStatement` is
  proved by `Langlands.Global.henniartGlobalizationExactStabilizerReduction`.
- `Langlands.Henniart.CandidateExistenceExactStabilizerReductionStatement` and
  its TC form `Langlands.Henniart.CandidateExistenceExactStabilizerTCReductionStatement`
  are proved by `Langlands.Henniart.candidateExistenceExactStabilizerReduction`
  and `Langlands.Henniart.candidateExistenceExactStabilizerTCReduction`.

The [LLC proof route](../henniart/llc-proof-route.md) places these in the
composite argument.

## Status

As of this pin, Proposition 4.8 is not proved in either form. The open
proofs of the new exact-stabilizer work are the prime branch (the reduction,
Task 8182, and the assembly, Task 8183, from the decomposition of Task 7785),
the singleton branch (Task 7786 revision 2, with Task 8232 to state the
restricted singleton reduction), the reduction (Task 8180) and the assembly
(Task 8181). The reductions also take reused inputs whose exact proofs are
still open. These include the two auxiliary parity inputs at positions 2 and
3: Task 8008 (`43773cdb-ef60-41ae-af67-d0af2841ac5b`) and Task 8009
(`85c6a682-6a41-4de3-a549-d368a770d640`). The published conditional
reductions behind them are not these proofs. The named external inputs are
also unproved: A1 (exact proof owner Task 7874), C2, B1–B4, B5r, restricted
B7, Arthur–Clozel III.4.2(c) (general form; the TC form is Task 7860) and the
general III.5.1 premise. Canonical B5, B6 and B7 are also unproved. Task
7340's planned derivations of them keep the general III.5.1 premise, with E2
for B5 and B6 and Arthur–Clozel I.6 for B6. They are not to be reported as
unconditional proofs. Under rulings `afc4eb77` (item 4) and `c05e16c6`, the
branches use the general III.5.1 premise only through B6, in the
distinctness lemma. Both reductions also list B6 itself at position 19.
