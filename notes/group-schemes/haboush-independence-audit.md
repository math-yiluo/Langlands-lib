# Geometric reductivity: dependency audit against the rank-one and dynamic-Borel exclusions

This note, dated 17 November 2026, records a Lean dependency audit of the Library proof of
[`ReductiveGeometricReductivityStatement`](../../Langlands/GroupScheme/Reductive/GeometricReductivityStatement.lean)
(Haboush's theorem). The audit checks that proof against the independence
restriction below, which the independent routes to geometric reductivity, to
`ReductiveLinearQuotientAffineStatement` and to `DynamicQuotientProperStatement`
must respect. The note also records some conditional reductions, one formal
consequence for the route of the proof, and a reading of the scope of the
excluded route. It does not prove geometric reductivity, and it does not certify
any route as independent. The audit results below refer to Library commit
`fcb85a7ef43356fec01e6ccf1605f08568c08cb0`.

## The restriction

The independent routes to geometric reductivity, to
`ReductiveLinearQuotientAffineStatement` and to `DynamicQuotientProperStatement`
all exclude five published propositions, their proofs and every result proved
downstream from them. The five propositions are
`ParabolicDynamicStatement`, `RegularCocharacterBorelStatement`,
`RankOneSolvableObstructionStatement`, `RankOneBorelDynamicStatement` and
`RankOnePositiveRootUniquenessStatement`. Their proof constants are
`parabolicDynamic`, `regularCocharacterBorel`, `rankOneSolvableObstruction`,
`rankOneBorelDynamic` and `rankOnePositiveRootUniqueness`. The explanation of
[`DynamicQuotientProperStatement`](../../Langlands/GroupScheme/Dynamic/QuotientProperStatement.md)
calls that proposition "a geometric prerequisite for the independent rank-one
positive-root argument". The independent route to
`ReductiveLinearQuotientAffineStatement` needs geometric reductivity as an input,
and the independent route to `DynamicQuotientProperStatement` needs
`ReductiveLinearQuotientAffineStatement`. The Library proves both, as
`reductiveLinearQuotientAffine` (`Reductive/LinearQuotientAffineProof.lean`) and
`dynamicQuotientProper` (`Dynamic/QuotientProperProof.lean`).

## Method

The audit computes a closure from a target constant. It follows, breadth first,
every constant that occurs in the type or the value of each reached constant,
including the values of theorems and opaque constants. The ten excluded constants
are leaves. Parent pointers give a shortest witness path to each excluded constant
that is reached. The scanner runs as a `#eval` inside a private module compiled
against the Library:

```lean
def deps (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci.value? (allowOpaque := true) with
  | some v => t ++ v.getUsedConstants
  | none => t
-- breadth-first search from `root`, recording `parent`, treating excluded names as leaves
```

The results below come from two runs of this scanner following type and value
and two runs following values only. This criterion is
conservative in one direction: a conditional lemma whose type
mentions an excluded proposition is flagged. It is blind in the other direction:
it sees named dependencies only. It cannot tell whether a new proof re-derives
the content of an excluded result, which matters for the exclusion of wrappers
(renamed or inlined reconstructions of an excluded argument). A constant without a value, such as a constructor or a recursor,
contributes only its type.

## Where the Haboush proof meets the exclusions

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
obstructions in the proof `reductiveGeometricReductivity`.

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
inputs, reaches none. The excluded rank-one proof goes through projective
prescribed Borel subgroups, and it stays excluded anyway.
So among the five, the rank-one exclusion is a requirement on proof provenance;
no excluded constant sits underneath it in the Library.

## Conditional reductions

Three conditional theorems reduce geometric reductivity to root-datum existence
and the Steinberg big cell.

- `splitSimplyConnectedCoverExistence_of_rootDatumExistence`:
  `RootDatumExistenceStatement → SplitSimplyConnectedCoverExistenceStatement`.
  It applies the minimal-lattice reduction, with `centralIsogenyRootDatumHom` and
  `semisimplePerfect` supplying its other two inputs.
- `IndependentHaboush.reductiveGeometricReductivity_of_splitCover_and_bigCell` and
  `IndependentHaboush.reductiveGeometricReductivity_of_rootDatum_and_bigCell`:
  `SplitSimplyConnectedCoverExistenceStatement`, respectively
  `RootDatumExistenceStatement`, together with `SteinbergBigCellStatement`, imply
  `ReductiveGeometricReductivityStatement`.

The closures of all three, and of the statements they mention, are clean. So
this architecture needs exactly two new independent proofs: root-datum
existence and the Steinberg big cell. The three theorems are in the Library:
`splitSimplyConnectedCoverExistence_of_rootDatumExistence` in
`SimplyConnected/SplitCoverOfRootDatum.lean`, the other two in
`Reductive/IndependentHaboushReduction.lean`. The Library has no proposition
`IndependentHaboush.RootDatumSteinbergReductionStatement` stating the
implication. It proves both inputs, as `rootDatumExistenceIndependent`
(`Reductive/RootDatumExistenceIndependent.lean`) and
`steinbergBigCellIndependent` (`Reductive/SteinbergBigCellIndependentProof.lean`).

## Root-datum existence implies rank-one uniqueness

The implication
`rankOnePositiveRootUniqueness_of_rootDatumExistence :
RootDatumExistenceStatement.{u} → RankOnePositiveRootUniquenessStatement.{u}`
holds (the Library has no theorem of this name). By `IsRootDatumOf`, the roots of `i` are the roots of a reduced root datum `P`.
Mathlib's `RootPairing.IsReduced.eq_or_eq_neg` says that two dependent roots of
`P` are equal or opposite. Opposite roots cannot both pair positively with one
cocharacter, because `latticePairing` is linear.

Consequently any proof of `RootDatumExistenceStatement`, in particular an
independent one such as `rootDatumExistenceIndependent`, contains a proof of the
rank-one positive-root content. The implication runs in one direction only. Deriving rank-one uniqueness
from an independently constructed root datum is a logical consequence. It is not
a dependency on the excluded proof, and it does not make such a root datum
inadmissible. The implication is an audit
observation and is not a premise of any assembly listed above. It does fix the
dependency order. Along the root-datum route the rank-one content is established
before geometric reductivity, and hence before the affine-quotient and properness
results (`ReductiveLinearQuotientAffineStatement`, `DynamicQuotientProperStatement`).
Properness is therefore not its first independent
source on that route. That is an obstruction to this route, not an
impossibility result. A positive-characteristic proof of geometric reductivity
that avoids root data would change this order. The sources examined in
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

## Scope clarification

The independence restriction excludes "the regular-cocharacter/Borel route". The
`DynamicQuotientProperStatement` explanation describes that route as Milne's
printed proof of Theorem 25.1 through Theorem 21.29 (regular cocharacters give
Borel subgroups). The scope of the exclusion is read as follows. It is a reading
only, neither dependency evidence nor a waiver.

- Ordinary Borel-subgroup results are not excluded as a class. They may serve as
  inputs when their actual type-and-value closures and their mathematical use avoid
  the five excluded inputs and the regular-cocharacter route. This reading does not
  check the list in the section on clean structural inputs.
- A new proof that the parabolic subgroup of a regular cocharacter is a Borel
  subgroup, feeding the Bruhat covering and the canonical dynamic assembly, still
  follows the excluded route, even if it avoids the old constant names.
- The independent proof of geometric reductivity need not avoid root data. A replacement for root-datum
  existence must not use the excluded rank-one statement, a proof of it, or a renamed
  or inlined reconstruction of the excluded argument, whether as an input or as an
  intermediate step.
