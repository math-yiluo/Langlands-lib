# Geometric reductivity: dependency audit against the rank-one and dynamic-Borel exclusions

Worker 169, 17 November 2026, Task 7298.

This note records a Lean dependency audit of the Library proof of
[`ReductiveGeometricReductivityStatement`](../../Langlands/GroupScheme/Reductive/GeometricReductivityStatement.lean)
(Haboush's theorem). The audit checks that proof against the independence
restriction of Task 7298 and of its host tasks, Task 7210 and Task 6453. The note
also records some conditional reductions that exist only as unreviewed drafts, and
one formal consequence for the current route. It does not prove geometric
reductivity, and it does not certify any route as independent. All Library
statements below refer to commit `fcb85a7ef43356fec01e6ccf1605f08568c08cb0`.

## The restriction

Task 7298, Task 7210 (`ReductiveLinearQuotientAffineStatement`) and Task 6453
(`DynamicQuotientProperStatement`) all exclude five published propositions, their
proofs and every result proved downstream from them. The five propositions are
`ParabolicDynamicStatement`, `RegularCocharacterBorelStatement`,
`RankOneSolvableObstructionStatement`, `RankOneBorelDynamicStatement` and
`RankOnePositiveRootUniquenessStatement`. Their proof constants are
`parabolicDynamic`, `regularCocharacterBorel`, `rankOneSolvableObstruction`,
`rankOneBorelDynamic` and `rankOnePositiveRootUniqueness`. The explanation of
[`DynamicQuotientProperStatement`](../../Langlands/GroupScheme/Dynamic/QuotientProperStatement.md)
calls that proposition "a geometric prerequisite for the independent rank-one
positive-root argument". Task 7210 needs geometric reductivity as an input, and
Task 6453 needs Task 7210.

## Method

The audit computes a closure from a target constant. It follows, breadth first,
every constant that occurs in the type or the value of each reached constant,
including the values of theorems and opaque constants. The ten excluded constants
are leaves. Parent pointers give a shortest witness path to each excluded constant
that is reached. The scanner runs as a `#eval` inside a private module compiled
with `lean_check`:

```lean
def deps (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci.value? (allowOpaque := true) with
  | some v => t ++ v.getUsedConstants
  | none => t
-- breadth-first search from `root`, recording `parent`, treating excluded names as leaves
```

The results below come from the diagnostics
`2bf48dcb-696c-44cc-8769-9b1217277d72` and `76fd4698-63dd-4075-8c05-724774979e41`
(type and value) and `237de8c6-5db2-4b46-8e14-063c62996b1e` and
`5b9fa036-1d13-4f04-8c96-9788bff096e2` (value only). This criterion is
conservative in one direction: a conditional lemma whose type
mentions an excluded proposition is flagged. It is blind in the other direction:
it sees named dependencies only. It cannot tell whether a new proof re-derives
the content of an excluded result, which matters for the "wrapper" clause of the
task contracts. A constant without a value, such as a constructor or a recursor,
contributes only its type.

## Where the current Haboush proof meets the exclusions

The proof `reductiveGeometricReductivity` is in
[`GeometricReductivityProof.lean`](../../Langlands/GroupScheme/Reductive/GeometricReductivityProof.lean).
In prime characteristic it uses `HaboushReduction.separator_fin_of_isAlgClosed`,
which consumes two tainted inputs.

1. **Simply connected cover.**
   `HaboushReduction.exists_simplyConnected_cover_of_isSemisimple →
   splitSimplyConnectedCoverExistence → rootDatumExistence →
   rootDatumExistence_of_splitWeylRationality → rootReducedness →
   RootReducedness.rankOneRootReducedness →
   RankOnePositiveRootUniquenessStatement`. The reflection data also reach
   `rootReducedness` through `SplitWeylRationality.exists_reflection` and
   `RankOneCentralizerDetection.kernelCentralizer_torusHom_eq_top`.
2. **Conjugation map** (`HaboushReduction.simplyConnectedConjugationMap`). This
   input uses `steinbergBigCell_of_rootAndCoroot` with `rootDatumExistence` and
   `splitCentralIsogenyExistence`, both tainted as in item 1. The Steinberg
   big-cell assembly reaches the exclusions in two further places:
   - the canonical ρ-Borel data
     (`SplitPinning.canonicalRhoBorelBigCellGeometricData`) use
     `IsRootDatumOf.bruhatCovering_polarization_rho → absoluteBruhatCovering`,
     whose proof uses `RegularCocharacterBorelStatement`, and
     `IsRootDatumOf.isBorelPair_polarization_rho → regularCocharacterBorel`;
   - the linked root parametrization uses
     `SplitPinning.linkedRootParametrization →
     SplitPinning.nonempty_linkedRootParametrization →
     exists_monic_rootRankOneRelations → splitRankOneRootCell →
     rankOnePositiveRootUniqueness`.

The scanner then treated `HaboushReduction.exists_simplyConnected_cover_of_isSemisimple`
and `HaboushReduction.simplyConnectedConjugationMap` as cut points. With those
cuts, the closures of `reductiveGeometricReductivity` (20,375 `Langlands`
constants) and `HaboushReduction.separator_fin_of_isAlgClosed` reach no excluded
constant. So the characteristic-zero branch, `reductiveCentralDerivedProduct`,
derived–central finiteness, the splitting of the central torus and
`separator_of_central_split_product` are clean. The two items above are the only
obstructions in the current proof.

## Clean structural inputs

Under the type-and-value scanner, each of the following published proofs has a
closure free of the ten excluded constants: `borelConjugacy`, `borelMaximalTorus`,
`solvableProperFixedPoint`,
`someBorelQuotientProper`, `parabolicSubgroupQuotientProper`,
`projectiveTorusFixedPointDimension`, `solvableMaximalTorusConjugacy`,
`solvableTorusQuotient`, `dynamicCentralizerReductive`,
`exists_proper_isBorelPair_of_relativeRoot`,
`RootReducedness.neg_mem_roots_of_rankOne`, `rootReducedness_of_rankOne`,
`centralIsogenyRootDatumHom`, `semisimplePerfect`,
`splitSimplyConnectedCoverExistence_of_minimalLattice`,
`exists_isMaximalTorus_isSplitTorus_of_isSepClosed`,
`reductiveCentralDerivedProduct`, `derivedCentralIntersectionFiniteness`,
`torusFiniteGaloisSplitting` and
`HaboushReduction.separator_of_central_split_product`. By contrast,
`dynamicFlagQuotientExistence` reaches `regularCocharacterBorel` through
`isParabolicSubgroup_of_range_eq_dynamicParabolic` and
`dynamicParabolicBorelData`.

The excluded proof `rankOnePositiveRootUniqueness` applies
`rankOnePositiveRootUniqueness_of_projectiveBorelInputs`. That theorem reaches an
excluded constant only through its own conclusion,
`RankOnePositiveRootUniquenessStatement`. Its value, and the value of each of its
inputs, reaches none. The Task 6453 contract states that the excluded rank-one
proof goes through projective prescribed Borel subgroups and that it stays
excluded anyway.
So among the five, the rank-one exclusion is a requirement on proof provenance;
no excluded constant sits underneath it in the Library.

## Conditional reductions (unreviewed drafts)

Task 7298 draft revision 4 holds three compiled conditional theorems. None of them
has been reviewed.

- `splitSimplyConnectedCoverExistence_of_rootDatumExistence` (Worker 169):
  `RootDatumExistenceStatement → SplitSimplyConnectedCoverExistenceStatement`.
  It applies the minimal-lattice reduction, with `centralIsogenyRootDatumHom` and
  `semisimplePerfect` supplying its other two inputs.
- `IndependentHaboush.reductiveGeometricReductivity_of_splitCover_and_bigCell` and
  `IndependentHaboush.reductiveGeometricReductivity_of_rootDatum_and_bigCell`
  (Worker 589): `SplitSimplyConnectedCoverExistenceStatement`, respectively
  `RootDatumExistenceStatement`, together with `SteinbergBigCellStatement`, imply
  `ReductiveGeometricReductivityStatement`.

The closures of all three, and of the statements they mention, are clean. So the
current architecture needs exactly two new independent proofs: root-datum
existence (Task 7458) and the Steinberg big cell (Task 7459).

## Root-datum existence implies rank-one uniqueness

The same draft proves
`rankOnePositiveRootUniqueness_of_rootDatumExistence :
RootDatumExistenceStatement.{u} → RankOnePositiveRootUniquenessStatement.{u}`.
By `IsRootDatumOf`, the roots of `i` are the roots of a reduced root datum `P`.
Mathlib's `RootPairing.IsReduced.eq_or_eq_neg` says that two dependent roots of
`P` are equal or opposite. Opposite roots cannot both pair positively with one
cocharacter, because `latticePairing` is linear.

Consequently any proof of `RootDatumExistenceStatement`, in particular an
independent one for Task 7458, contains a proof of the rank-one positive-root
content. The current route to geometric reductivity therefore cannot feed an
independent rank-one argument through Tasks 7210 and 6453 without first having
one. That is an obstruction to the current route, not an impossibility result. A
positive-characteristic proof of geometric reductivity that does not pass through
root data would avoid it, and so would a rank-one argument that does not use
Task 6453. The sources examined in
[the dynamic quotient source map](dynamic-quotient-source-map.md) (Seshadri,
Steinberg, the Chevalley seminar) all use root data or rank-one root-subgroup
geometry.

## Survey of published statement proofs

A cheaper value-only variant of the scanner was run over every theorem in
`Langlands.GroupScheme` whose type is headed by a `…Statement` proposition. It
imported 657 modules containing such proofs; the `IntegralModel` modules and
`EtaleLocalSplitProof`/`RelativeCenterProof` were left out because their
instances clash. Conditional theorems, whose types are implications, are not
counted.
It found 948 such theorems: 666 clean and 282 tainted. By excluded input
(P, R, S, B, U for the five propositions in the order listed above), the tainted
counts are P 30, R 25, S 1, B 1, U 75, PR 9, PU 1, RS 2, RU 117 and PRU 21. The
tainted ones include `rootReducedness`, `rootDatumExistence`,
`splitSimplyConnectedCoverExistence`, `splitCentralIsogenyExistence` and
`splitRankOneRootCell` (U), `absoluteBruhatCovering`,
`dynamicFlagQuotientExistence` and `maximalSplitTorusConjugacy` (R), and
`steinbergBigCell` and `reductiveGeometricReductivity` (RU).
Most results built on the root datum are tainted, so independent work should
check a candidate input with the type-and-value scanner before using it.

## Open scope question

The contracts exclude "the regular-cocharacter/Borel route". The
`DynamicQuotientProperStatement` explanation describes the unavailable route as
Milne's printed proof of Theorem 25.1 through Theorem 21.29 (regular cocharacters
give Borel subgroups). Ordinary Borel-subgroup geometry, such as the clean proofs
listed above, is not excluded by name. Whether a new rank-one or
root-datum argument may be built from it, and how that would differ from the
excluded projective-prescribed-Borel proof, has been asked of the Task 7298
publisher; no answer is recorded here.
