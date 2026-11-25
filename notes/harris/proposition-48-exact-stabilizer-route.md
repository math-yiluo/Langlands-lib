# Harris 1998 Proposition 4.8 under the exact-stabilizer condition: statements, reduction and proof status

This note maps the Library's restatement of Harris 1998, Proposition 4.8,
and of its induction, with Harris's condition (4.12) on the auxiliary
character (`Langlands.Global.GeneralPosition.HasExactWeilStabilizer`) in
place of general position. It also covers the interfaces B5, B6 and B7 of
the plan note (source `operator-external-inputs-plan-2026-11-16`, Section 2.2,
Section 4.8 with Remark 4.2).

The first table lists the new statements and definitions of this
formulation; only the general form of III.4.2(c) there is an earlier Library
statement. The reduction also reuses Library statements of the
general-position formulation: the auxiliary parity inputs, the Mackey step,
A1, C2, isobaric invariance and the old transfer inputs B1–B4 (positions 2,
3, 5 and 11–17 of the second table), and the general III.4.2(c) (position 20).
The proof column of each table gives the proof status in the Library. The
general-position formulation is in the [Proposition 4.8 route](proposition-48-route.md).
That formulation and the Drinfeld-tower proof of the comparison A2 remain as
the fallback; neither was weakened. The theorem
`proposition48ExactStabilizerStatement_of_proposition48Statement`
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

- **B6 as stated.** B6 is stated as in the plan note, Section 2.2, not as
  the variant in Remark 4.2. The reason is that the published
  branch hypotheses give solutions for the immediate Mackey children only,
  while the variant needs solutions along a whole tower. In return, the
  planned derivation of B6 needs the general III.5.1 premise described below,
  not only a restricted form of III.5.1.
- **Further design decisions.** They are referred to below by these labels.
  - D1: B7 is stated literally, and the archimedean bridge is a separate
    named premise.
  - D2: B6 and B7 are canonical statements with no E2 or III.5.1 hypothesis
    inside them. Arthur–Clozel III.5.1 in the generality of the source
    becomes its own named, unproved premise. The branches use B6 only
    through the distinctness lemma (claim (2) of Remark 4.2), and B7 only in
    a restricted form.
  - R2: solutions of the restated induction carry their complex-place
    parameters.
  - D3: B5r is stated beside B5. The singleton branch uses B5r, with the
    conjugate place as the second finite place. Canonical B5 stays in the
    Library and is not used by the branches.
- **The general III.5.1 premise.** It is stated as
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
- **General and restricted proof programs.** Under decisions D2 and D3,
  canonical B5, B6 and B7 rest on the general premise; they are to be
  derived from it only conditionally. The general premise is beyond the
  simple trace formula; the restricted forms are not. So the restricted
  route stays the intended end. The branches use B5r, the restricted B7 and
  the distinctness lemma, and the general premise enters them only through
  B6 in that lemma. The restricted III.5.1
  (`RestrictedCyclicBaseChangeCompatibilityStatement`) is a separate
  statement, not the general premise. The whole-tower variant of B6 is to be
  decided once that restricted III.5.1 is proved (D2).

## Statements and their proof status

| Item | Declarations (module) | Proof |
| --- | --- | --- |
| B5 | `CyclicWeakBaseChangeSupercuspidalStatement` and TC `CyclicWeakBaseChangeSupercuspidalTCStatement` (both in `CyclicWeakBaseChangeSupercuspidalStatement`) | open; its recorded route is only a conditional derivation from the general III.5.1 premise at `v` with E2, after B5r (D3) |
| B5r | `RestrictedCyclicWeakBaseChangeSupercuspidalStatement` and TC `RestrictedCyclicWeakBaseChangeSupercuspidalTCStatement` (both in `RestrictedCyclicWeakBaseChangeSupercuspidalStatement`) | open; its recorded route is the twisted simple trace formula, with E2 (local descent of σ-stable supercuspidal classes) and the fibre statement (Arthur–Clozel III.3.1) as inputs (D3) |
| B6 | `TowerBaseChangeHeckeComponentStatement` and TC `TowerBaseChangeHeckeComponentTCStatement` (both in `TowerBaseChangeHeckeComponentStatement`); vocabulary `PrimeCyclicBaseChangeTower` | open; its recorded route is a conditional derivation from the general III.5.1 premise with E2 and Arthur–Clozel I.6 (D2) |
| III.4.2(c) | general `CyclicPrimeIsobaricBaseChangeStatement` (module `IsobaricCyclicTransferStatement`, earlier); TC `CyclicPrimeIsobaricBaseChangeTCStatement` (its own module `CyclicPrimeIsobaricBaseChangeTCStatement`) | general form: unproved external input, Arthur–Clozel III Thm 4.2(c), p. 202; TC form: open (the Library has the conditional `cyclicPrimeIsobaricBaseChangeTC_of_cuspidal` in `CyclicPrimeIsobaricBaseChangeTCAssembly`) |
| III.5.1 (general premise) | `CyclicStrongBaseChangeSupportStatement` (one form only): the support-and-parameter consequence of Arthur–Clozel III.5.1 for general unitary isobaric data ([Markdown](../../Langlands/Automorphic/Unramified/CyclicStrongBaseChangeSupportStatement.md)). Its nonsplit clause takes a σ-lift-certified local map and a downstairs support witness | unproved external input (D2). It is not the restricted III.5.1 `RestrictedCyclicBaseChangeCompatibilityStatement` |
| B7 | `CyclicWeakBaseChangeComplexPlaceStatement` and TC `CyclicWeakBaseChangeComplexPlaceTCStatement` (both in `CyclicWeakBaseChangeComplexPlaceStatement`); vocabulary of complex-place parameter transport, sums over actual places and complex-place parameters of isobaric constituent data | open; its recorded route is a conditional derivation from the general III.5.1 premise at the complex places (D2). Not used by the branches |
| restricted B7 | `RestrictedCyclicWeakBaseChangeComplexPlaceStatement` (one form only) | open |
| bridge | `Langlands.Automorphic.CuspidalComplexParameterBridgeTCStatement` (TC form only, module `Automorphic/CuspidalComplexParameterBridgeStatement`); vocabulary of complex exponents, shifted highest weights and Clozel regularity | proved: `Langlands.Automorphic.cuspidalComplexParameterBridgeTC` (`Automorphic/CuspidalComplexParameterBridgeProof`) |
| datum and validity | `IsProposition48ExactStabilizerDatum`, `Proposition48Problem.{IsExactStabilizerValid, IsExactStabilizerValidAtParity, IsAuxiliaryExactStabilizerValidAtParity, IsAuxiliaryExactStabilizerValid}` with forgetful lemmas (`HarrisProposition48ExactStabilizerData`) | definitions |
| restated proposition | `Proposition48ExactStabilizerStatement` (`HarrisProposition48ExactStabilizerStatement`) | open (the Library has the conditional `proposition48ExactStabilizerStatement_of_proposition48Statement`, from `Proposition48Statement`) |
| inheritance | `Proposition48ExactStabilizer{Mackey,Parity}InheritanceStatement` (`HarrisProposition48ExactStabilizerInheritanceStatement`) | proved: `proposition48ExactStabilizerMackeyInheritance`, `proposition48ExactStabilizerParityInheritance` |
| parameter data | `Proposition48Problem.{IsInducedComplexPlaceParameter, HasInducedComplexPlaceParameters, HasParameterSolution, IsMackeyConstituent, HasDistinctMackeyComponents}` (`HarrisProposition48ExactStabilizerParameterData`) | definitions |
| rank one, untwist | `Proposition48ExactStabilizerAuxiliaryRankOneStatement`, `Proposition48ExactStabilizerParameterUntwistStatement` (`HarrisProposition48ExactStabilizerParameterAuxiliaryStatement`) | proved: `proposition48ExactStabilizerAuxiliaryRankOne`, `proposition48ExactStabilizerParameterUntwist` |
| distinctness | `Proposition48ExactStabilizerDistinctnessStatement` and TC `...DistinctnessTCStatement` (both in `HarrisProposition48ExactStabilizerDistinctnessStatement`) | proved: `proposition48ExactStabilizerDistinctness`, `proposition48ExactStabilizerDistinctnessTC` |
| prime branch | `Proposition48ExactStabilizerPrimeBranchStatement` and TC `...PrimeBranchTCStatement` (both in `HarrisProposition48ExactStabilizerBranchStatement`) | open; its proof is divided into the reduction statements `Proposition48ExactStabilizerPrimeBranchReductionStatement` and its TC form (`HarrisProposition48ExactStabilizerPrimeBranchReductionStatement`, unproved) and an exact assembly |
| singleton branch | `Proposition48ExactStabilizerSingletonBranchStatement` and TC `...SingletonBranchTCStatement` (both in `HarrisProposition48ExactStabilizerBranchStatement`) | open; its recorded route is a corollary of the restricted branch: B5 implies B5r |
| restricted singleton branch | `Proposition48ExactStabilizerRestrictedSingletonBranchStatement` and TC `...RestrictedSingletonBranchTCStatement` (both in `HarrisProposition48ExactStabilizerRestrictedDescentStatement`) | open; the Library states no reduction of it to named inputs |
| reduction | `Proposition48ExactStabilizerReductionStatement` and TC `...ReductionTCStatement` (both in `HarrisProposition48ExactStabilizerReductionStatement`) | open; planned as a corollary of the restricted reduction |
| restricted reduction | `Proposition48ExactStabilizerRestrictedReductionStatement` and TC `...RestrictedReductionTCStatement` (both in `HarrisProposition48ExactStabilizerRestrictedDescentStatement`) | open |

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

**The planned singleton route.** The restricted singleton branch is to be
proved first. In the Mackey case with one double coset, the branch
applies TC B5r to every weak descent, in both orders, at the auxiliary
conjugate pair: `v = Q.Ps.v` and the second finite place
`v' = conjPlace Q.E Q.Ps.v`. The two places differ because `p` splits in `K₀`
(the named input `SplitPlaceNeConjPlaceStatement`). The validity clauses of the
problem give unique places of `Q.L` above both, hence unique places of the
prime cyclic step `D` above both. One cuspidal presentation of the lift is
supercuspidal at both places. A reduction of the TC restricted branch to
thirteen named inputs along these lines is planned; the Library does not
state it. The published singleton branch and
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

| Pos. | Declaration | Source | Proof status |
| --- | --- | --- | --- |
| 1 | `Proposition48ExactStabilizerAuxiliaryRankOneStatement` | internal (R2) | proved |
| 2 | `Proposition48AuxiliaryParityNormalizationStatement` | general-position input | no theorem; it follows from proved results: `proposition48AuxiliaryParityNormalizationReduction` with `normTwistInfinity`, `cmNormConjugation`, `proposition48PlaceNormTwist` and `generalPositionAmbientTwist` |
| 3 | `Proposition48AuxiliaryParityUntwistStatement` | general-position input | no theorem; it follows from proved results: `proposition48AuxiliaryParityUntwistReduction` with `heckeDeterminantTwistWeakInduction`, `heckeDeterminantTwistConjugateSelfDual` and `heckeDeterminantTwistSupercuspidal` |
| 4 | `Proposition48ExactStabilizerParameterUntwistStatement` | internal (R2) | proved |
| 5 | `Proposition48MackeyStepStatement` | general-position input | proved: `proposition48MackeyStep` |
| 6 | `Proposition48ExactStabilizerMackeyInheritanceStatement` | plan note Section 4.8 | proved |
| 7 | `Proposition48ExactStabilizerParityInheritanceStatement` | plan note Section 4.8 | proved |
| 8 | `Proposition48ExactStabilizerDistinctnessStatement` | plan note Remark 4.2 (2) | proved |
| 9 | `Proposition48ExactStabilizerPrimeBranchStatement` | Harris pp. 201–203 | open |
| 10 | `Proposition48ExactStabilizerSingletonBranchStatement`; restricted: `Proposition48ExactStabilizerRestrictedSingletonBranchStatement` | Harris pp. 201–203 | open (both) |
| 11 | `Langlands.GaloisRepresentation.Harris1998Theorem12CuspidalStatement` (A1; module `Langlands/Galois/Harris1998ExistenceStatement`) | general-position input (Harris Thm 1.2) | open |
| 12 | `CuspidalSpectralRigidityStatement` (C2) | general-position input | open (the Library has the conditional `cuspidalSpectralRigidityLandauReduction`, from `CuspidalPairPoleStatement` with the proved `cuspidalPairAbsoluteConvergence`) |
| 13 | `Proposition48IsobaricInvarianceStatement` | general-position input | proved: `proposition48IsobaricInvariance`, TC `proposition48IsobaricInvarianceTC` |
| 14 | `CyclicRegularInductionStatement` (B2) | general-position input | open (the Library has the conditional `cyclicRegularInductionNormReduction`, from `CyclicRegularInductionExistenceStatement` and `CuspidalEulerConstituentRecoveryStatement`) |
| 15 | `CyclicRegularOrbitLiftStatement` (B3) | general-position input | open (the Library has the conditional `cyclicRegularOrbitLiftReduction`, from `CyclicRegularInductionExistenceStatement`, `WeakInductionOrbitBaseChangeStatement` and `CyclicWeakBaseChangePairMultiplicityStatement`) |
| 16 | `CyclicStableDescentStatement` (B1) | general-position input | open |
| 17 | `CyclicWeakInductionSupercuspidalStatement` (B4) | general-position input | open (the Library has the conditional `cyclicWeakInductionSupercuspidal_of_matching_at_completion`) |
| 18 | `CyclicWeakBaseChangeSupercuspidalStatement` (B5); restricted: `RestrictedCyclicWeakBaseChangeSupercuspidalStatement` (B5r) | plan note Section 2.2; D3 | open (both; see the first table) |
| 19 | `TowerBaseChangeHeckeComponentStatement` (B6) | plan note Section 2.2 | open; its recorded route is conditional on the general III.5.1 premise |
| 20 | `CyclicPrimeIsobaricBaseChangeStatement` (III.4.2(c)) | Arthur–Clozel III Thm 4.2(c) | general form unproved; TC form open |
| 21 | `RestrictedCyclicWeakBaseChangeComplexPlaceStatement` (restricted B7) | plan note Section 2.2, D2 | open |
| 22 | `Langlands.Automorphic.CuspidalComplexParameterBridgeTCStatement` (bridge) | D1 | proved: `Langlands.Automorphic.cuspidalComplexParameterBridgeTC` |

Positions 2, 3, 5 and 11–17, and the general form at position 20, are
existing Library statements reused from the general-position formulation;
the [Proposition 4.8 route](proposition-48-route.md) describes them. Compared with `Proposition48ReductionStatement`, the
reduction drops A2 and replaces the rank-one input and the two branches. It adds
positions 4, 6–8 and 18–22.

## Reuse of the general-position proofs

Of the proofs of the general-position formulation, those of parity
normalization and untwist (positions 2, 3), of the Mackey step (position 5)
and of isobaric invariance (position 13) serve the exact-stabilizer route
unchanged. Rank one, the prime and singleton branches, the reduction and the
final assembly have second versions here: the parameter form of rank one
(proved), the restated branches, `Proposition48ExactStabilizerReductionStatement`
(whose proof can reuse the helpers of the proved `proposition48Reduction`) and
the restated proposition. The proof of A2 is not needed by the
exact-stabilizer route and remains open as the fallback. The
general-position statements keep their original targets.

## Consumers

Henniart's uses of the restated proposition are stated as follows; the
datum statement and the reductions are proved.

- `Langlands.Global.HarrisDatumCharacterRealizationExactStabilizerStatement`:
  proved by `Langlands.Global.harrisDatumCharacterRealizationExactStabilizer`.
  It supplies Henniart's datum characters with the exact Weil stabilizer.
- `Langlands.Global.HenniartGlobalizationExactStabilizerStatement`: the
  restated proposition implies `Langlands.Global.RelativeGaloisGlobalization`.
  It is unproved. Its reduction
  `Langlands.Global.HenniartGlobalizationExactStabilizerReductionStatement` is
  proved by `Langlands.Global.henniartGlobalizationExactStabilizerReduction`.
- `Langlands.Henniart.CandidateExistenceExactStabilizerReductionStatement` and
  its TC form `Langlands.Henniart.CandidateExistenceExactStabilizerTCReductionStatement`
  are proved by `Langlands.Henniart.candidateExistenceExactStabilizerReduction`
  and `Langlands.Henniart.candidateExistenceExactStabilizerTCReduction`.

The [LLC proof route](../henniart/llc-proof-route.md) places these in the
composite argument.

## Status

Proposition 4.8 is not proved in either form. The open proofs of the new
exact-stabilizer work are the prime branch (its reduction statements and an
exact assembly), the singleton branch (with a reduction of the restricted
singleton branch still to be stated), the reduction and the final assembly.
The reductions also take reused inputs whose exact proofs are open,
including the two auxiliary parity inputs at positions 2 and 3; the
conditional reductions behind them in the Library are not these proofs. The
named external inputs are also unproved: A1, C2, B1–B4, B5r, restricted B7,
Arthur–Clozel III.4.2(c) (general form; the TC form has only a conditional
assembly) and the general III.5.1 premise. Canonical B5, B6 and B7 are also
unproved. Their planned derivations keep the general III.5.1 premise, with E2
for B5 and B6 and Arthur–Clozel I.6 for B6; they are not to be reported as
unconditional proofs. Under decisions D2 and D3, the branches use the
general III.5.1 premise only through B6, in the distinctness lemma. Both
reductions also list B6 itself at position 19.
