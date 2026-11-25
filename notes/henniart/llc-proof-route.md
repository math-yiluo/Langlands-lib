# Local Langlands for GL_n: published reductions and the remaining premises

This note has dated versions. First version 10 November 2026, second
version 11 November 2026, third, fourth and fifth versions 12 November
2026, sixth to thirteenth versions 13 November 2026, fourteenth to
sixteenth versions 14 November 2026, seventeenth to nineteenth versions 15
November 2026, twentieth to twenty-third versions 17 November 2026,
twenty-fourth to twenty-sixth versions 18 November 2026, twenty-seventh
and twenty-eighth versions 19 November 2026, twenty-ninth version 20
November 2026.

**Snapshot.** At Library commit `d6b462beebdb629f6b6746bdf0698a800d84104f`
the full correspondence still reduces to two open premises: candidate
existence and numerical surjectivity. All four totally complex reduction
links (D and links 1–3) now have published proofs. In Harris's
exact-stabilizer route, the new arithmetic spectral transport proof
supplies the remaining added premise of the two distinctness reductions,
but the two branch targets and the 22-input reduction of Proposition 4.8
still lack proofs. On the numerical side, the compatible injections (I4)
and tower lemma now have published statements, and integrality of the Weil
Artin conductor is proved. Neither of the two main premises is discharged.

Statements of this note about what the Library proves are of the Library
commit named with them, the latest being
`d6b462beebdb629f6b6746bdf0698a800d84104f`. The closing section "Present
status of the statements named in this note" gives, for every statement
that the note names, its status in the Library as it is now.

For the totally complex completed equation (A2), two Lean-checked
compositions below show that the two complex local functional equations
and the two *unrestricted* pointwise factorizations suffice. The equal-rank
local equation now reduces to meromorphic continuation and the identity of
the continuations, with the growth input proved. Replacing the unrestricted
equal-rank pointwise factorization by its Whittaker slice reduction exposes
a real-place test dependence. That is different from the real-place
functional equation, which neither composition uses.

The twenty-eighth version was published at
`d6b462beebdb629f6b6746bdf0698a800d84104f` and was checked against Library
commit `24390f9f6d7a3b7df9e5b9dd4d6e79e178c8ac85`. The twenty-seventh
version was published at commit
`ecb96e554fed652972a5c0308d69b041f6bc54e4`. Between commits `ecb96e55` and
`24390f9f` the Library added 404 Lean modules, removed none and changed
twelve Lean files. One changed file is named in this note:
`Global/RankinSelberg/ComplexGodementCompact`, whose full-row-rank
hypothesis is now the predicate
`Langlands.RankinSelberg.AdjacentRankFullRank` of the new module
`Representation/RankinSelberg/AdjacentRankCompactOrbit`. What this note
says of that module, that it proves lemmas and no premise, still holds.
The other eleven changed files are outside the scope of this note. The
following added modules bear on this note: the proof of
`CandidateExistenceExactStabilizerTCReductionStatement`, from which the
published totally complex reduction statement D
(`Henniart.CandidateExistenceTCReductionStatement`) follows, so that the
third theorem of the composite no longer assumes it and a fifth theorem is
added; the reduction statement of the exact-stabilizer form of Harris's
Prop. 4.8 to 22 named inputs; the proof of
`LocalFactor.ComplexArchimedeanTateStatement` on the chain of input A2 of
premise 1; under premise 2, the local cyclic base-change statement (I3),
the proofs of the polar-part closed formula and counting identity, the
reduction statement of the twist Swan bound and proofs of three
Bushnell–Kutzko statements; the proof of `KummerTowerUpperSupStatement`;
and statements of the trace formula and base-change program for input
(I3). Each is described where the note names it. No premise of the route
is proved at commit `24390f9f`. Five further statements and proofs on the route were not
in the Library at commit `24390f9f`: the proofs of D and of link 3
(`Henniart.CandidateExistenceTCReductionStatement`,
`RelativeWeilGroup.AssociatedCuspidalFactorReductionTCStatement`) and the
statements of the truncated Weil-side elementary layer, of the
rank-bounded premise (I4) and of the base case of the numerical descent.
They are described where the note names them.

The twenty-seventh version was checked against Library commit
`86dbe494f42945f32e487976003611ce4579e721`. The twenty-sixth version was
published at commit `7e12a30cd33f6905b3d1d7477b73eaff3c7342b3`. Between
commits `7e12a30c` and `86dbe494` the Library added and changed no Lean
file; it added one public note, under `notes/errata/`, that this note does
not use. Between commits `f050c0b1` and `7e12a30c` (through commit
`c0148597`) the Library added 226 Lean modules and changed ten Lean files,
none of which this note names. The following added modules bear on this
note: two proofs of the totally complex form of input A1 of premise 1, so
that this input is proved in that form; further reductions on the chain of
input A2 of premise 1, among them a reduction of the equal-rank conjunct
of `ArchimedeanFactorizationStatement` to one archimedean statement; the
statement (LD) and the proof of `RefinedStrataStatement`, both under
premise 2; the proof of `KummerStepHerbrandPsiStatement`; and further
statements of the trace formula and base-change program for input (I3).
Each is described where the note names it. No premise of the route was
proved at commit `86dbe494`.

The twenty-sixth version was checked against Library commit
`f050c0b1b525624bc32c1e7c25a8d2841bb2d4e0`. The twenty-fifth version was
published at commit `ba9d1e9ac8e4b6f239a8bbf0ba15e6743fd140c9`. Between
commits `8aede86c` and `ba9d1e9a` the Library added 495 Lean modules and
changed four Lean files, none of which this note names. Between commits
`ba9d1e9a` and `f050c0b1` it added 433 Lean modules and changed 21 Lean
files. Four of the changed files are the level statements L0, L1, L2 and
T2, which this note names: only the names of their local instances
changed, so that the four modules can be imported together, and their
statements and Markdown are unchanged. One changed file alters a
definition: `BushnellKutzko.Stratum.IsDefiningSequence` (module
`BushnellKutzko/DefiningSequence`) now asks that each member of a defining
sequence have the hereditary order of the original stratum
(`chain.order`), where it asked before for the same lattice chain. The
approximation statement (2.4.1), `StratumApproximationStatement`, uses
this predicate. The other 16 changed files are outside the scope of this
note. The following modules added between `8aede86c` and `f050c0b1` bear
on this note: the proof of `ComplexGenericStandardParameterStatement`
(input A1 of premise 1); proofs of the three remaining unrestricted
premises that the totally complex (G') needs on the chain of input A2, so
that all eight are proved, and of further premises and reductions for
`ArchimedeanFactorizationStatement` and
`ComplexPlaceFunctionalEquationStatement`; proofs of three of the five
propositions on Henniart's uses of the exact-stabilizer form of Harris's
Prop. 4.8 and of both inheritance statements of that form, together with
its branch statements, distinctness statement and rank-one and untwist
statements (premise 1); the statements (I1) and the twist Swan bound
(premise 2); the proofs of `BushnellKutzkoLabelCountStatement`,
`KummerStepUpperSupStatement` and `CyclicNormKernelCharacterStatement`;
and statements of the trace formula and base-change program for input
(I3). Each is described where the note names it. No premise of the route
is proved at commit `f050c0b1`. The twenty-sixth version also added a
fourth theorem to the composite Lean module (section "The composite"),
which uses Harris's Prop. 4.8 in its exact-stabilizer form.

The twenty-fifth version was checked against Library commit
`8aede86c1ec386cf08cfb29e80ce3c58a3239cd8`, at which the twenty-fourth
version was published. Between commits `d26f6985` and `8aede86c` the
Library added 239 Lean modules and changed nine Lean files, none of which
this note names. The following added modules bear on this note: the proof
of `ChebotarevRigidityStatement` (item 5 of "Operator decisions of 16
November 2026"); the three statement modules on Henniart's uses of the
exact-stabilizer form of Harris's Prop. 4.8 (premise 1); proofs of three
of the eight unrestricted premises that the totally complex (G') needs on
the chain of input A2 of premise 1; and four modules under
`BushnellKutzko/` that state, without proof, the refinement theorem
(2.2.8) and the approximation of pure strata (2.4.1) of Bushnell–Kutzko
(1993), with their definitions. No premise of the route is proved at
commit `8aede86c`. The twenty-fourth version was checked against commit
`d26f6985162bcc4b604d91d2fd1c35df9c7ce13c`. The twenty-third version was
published at commit `70eba6bb71c0dfc732a95146e6f12219c3cc76ae`. Between
commits `ab9053b1` and `70eba6bb` the Library added 250 Lean modules and
changed one Lean file, under `GroupScheme/Torus/`, that this note does not
name. Among the added modules is base-change infrastructure for input (I3)
(modules under `BaseChange/`: the norm map and the cyclic norm lemma
statement; cusp forms, with two statements on them; and Satake characters
and the unramified base-change homomorphism of spherical Hecke algebras,
with a statement on each). The module `BaseChange/UnramifiedHecke` defines
the Satake-character predicate `IsSatakeCharacter` and the predicate
`IsUnramifiedBaseChangeHom`; it does not define the spherical Hecke
algebra, which it reuses: that algebra is
`Langlands.Unramified.SphericalHeckeAlgebra`, declared in
`Representation/Unramified/HeckeOperators` and already in the Library at
commit `ab9053b1`. The import closure of the composite Lean module of this
note (its theorems, in the section "The composite") contains no
`BaseChange/` module. Two statements named in this note reuse the
base-change vocabulary: `SatakeCharacterStatement`, itself one of the
added modules, is stated with `SphericalHeckeAlgebra` (declared in
`Representation/Unramified/HeckeOperators`) and `IsSatakeCharacter`
(declared in `BaseChange/UnramifiedHecke`); and `RegularTransferStatement`
(added after `70eba6bb`) assumes the predicate `IsCyclicAlgebra` of
`BaseChange/Norm` and uses the concordance predicate `AreConcordant` of
`BaseChange/OrbitalIntegral`, which is defined through the norm
`cyclicNorm` and the predicates `IsNorm` and `IsNormAssociated` of
`BaseChange/Norm`. Between commits `70eba6bb` and `d26f6985` the Library
added 1281 Lean modules and changed ten Lean files, none of which this
note names. The following is a selection of the added modules that bear on
this note: the refined strata of Option II, which removes the bottleneck
that the twenty-third version reported (premise 2); the vocabulary of
actual local components and supercuspidal support of isobaric data and the
norm-kernel character statement (the program for input (I4)); the
statements B5, B6 and B7 and the restated Harris Prop. 4.8 with its
inheritance statements and parameter data (premise 1); a totally complex
companion and further proofs and reductions on the chain of input A2 of
premise 1; the proofs of `FiniteGaloisFrobeniusRigidityStatement` and
`HerbrandPsiTruncationStatement`; and statements named in this note,
namely the Kummer-stage quotient statements (module
`LocalFactor/Ramification/Herbrand/TruncationQuotientStatement`), the
Bushnell–Kutzko label count (module
`Correspondence/BushnellKutzkoLabelCount`), the level statements L0, L1,
L2 and T2 (four modules under `BushnellKutzko/`) and the regular transfer
statement of cyclic base change (module
`BaseChange/RegularTransferStatement`). Each is described where the note
names it. No premise of the route is proved at commit `d26f6985`. The
twenty-third version was checked against commit
`ab9053b1751d6b6557d044c38c04e4c8a67dfffc`. Between commits `b369a8f2` and
`ab9053b1` the Library added 595 Lean modules and changed one Lean file,
under `BruhatTits/IntegralModels/`, that this note does not name. The
added modules that bear on this note are: the proof of the archimedean
central sign identity and four reductions on the chain of input A2 of
premise 1; the datum and validity predicates of the exact-stabilizer form
of Harris's Prop. 4.8 and the vocabulary of towers of prime cyclic
extensions (premise 1); the polar-part model of Option II (premise 2); the
statements of the Kummer-tower program and the proof of Chebotarev's
theorem in prime-realization form (see "Operator decisions of 16 November
2026"). Each is described where the note names it. The twenty-second
version was checked against commit
`b369a8f280229cf081a17f96b81c7a8c1ff1f539`. Between commits `fcb85a7e` and
`b369a8f2` the Library added 268 Lean modules and changed six Lean files,
under `BruhatTits/IntegralModels/` and `GroupScheme/`, that this note does
not name. Three of the added modules bear on this note. One proves
`LocalClassField.FiniteAbelianReciprocityTheorems` (see item 3 of
"Operator decisions of 16 November 2026"). The other two are reductions on
the totally complex chain of input A2 of premise 1. A search of the added
modules for the names of the propositions of this note found no other
mention of them. The twenty-first version was checked against commit
`fcb85a7ef43356fec01e6ccf1605f08568c08cb0`. Between commits
`9e39a73d21bd6ed6fac00b01cc5e01c0db5d105b` and `fcb85a7e` the Library
changed no Lean file; it changed notes, among them the twentieth version
of this note, and the wiki index. The twentieth version was checked
against commit `9e39a73d`. Its text was first checked against commit
`314cfd1a0275806b9ff4281f3d3e51a05e9a6cb5`, and the Lean facts that it
states at commit `314cfd1a` also hold at commit `9e39a73d`: between the
two commits the Library added 131 Lean modules and changed seven Lean
files, none of which this note names, and none of the added modules
mentions a proposition that this note names. The nineteenth version was
checked against commit `72480b70c88adff84a438bd7029d64ee3977469c`, the
eighteenth against commit `fab9caeae532b7a65e67e702bcab72d3194371ae`, and
the seventeenth against commit `5764b3a9`, which has the same Lean sources
as commit `544dba099880b57da5fdc3cbc715c01cf2579eb2`. Between commits
`5764b3a9` and `72480b70`, the Library added Lean modules and changed
seven Lean files that this note does not name. The added modules that bear
on this note are the two statements on the chain of premise 3 below,
`Conductor.ConductorMinimalityProof`, the proof of
`SupercuspidalOrbitStratumFinitenessStatement` under premise 2 and the
proof of `Conductor.supercuspidalPadicConductorExponent` under premise 3.
Between commits `72480b70` and `314cfd1a`, the Library added 1584 Lean
modules and changed nine Lean files, all under `BruhatTits/`,
`Geometry/Building/` and `GroupScheme/`, that this note does not name. The
added modules that bear on this note are the proof of
`Henniart.Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor`
(see "Published: the two-premise entry" below), the totally complex
statements and reductions under premise 1, and the proofs of Tadić's
exhaustion of the unitary dual and of the exhaustion of unitary generic
representations (input 2 of premise 1). A search of the Lean files added
since commit `5764b3a9` for the names of the open propositions of this
note found no other proof of them. So the Lean facts that this note states
at commit `544dba09` also hold at commit `314cfd1a`, except where the text
says otherwise.

This note records how the published Library reduces the full local
Langlands correspondence for GL_n to two propositions, candidate existence
and numerical surjectivity. The newest published reduction of the
supercuspidal correspondence,
`Henniart.Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor`,
has three premises: these two and the supercuspidal p-adic variant of the
conductor exponent theorem of Jacquet–Piatetski-Shapiro–Shalika (JPSS).
The variant is proved, by `Conductor.supercuspidalPadicConductorExponent`.
The first theorem of the composite Lean module below combines these two
theorems with the published passage from the supercuspidal to the full
correspondence. It proves the full correspondence from candidate existence
and numerical surjectivity alone. The module has been compiled as a
development check but is not published. Neither of the two open
propositions has a proof at commit `d6b462be`. The general JPSS conductor
exponent statement, the third premise of the earlier three-premise
theorem, is no longer needed on the route; see "Statements that left the
route".

The Library also proves a reduction of the first premise, candidate
existence, to five global inputs: `Henniart.candidateExistenceReduction`.
It gives candidate existence only with the automorphic-lattice universe
equal to `0`. One of the five inputs, local relative class formation, is
proved. So the composite module has a second theorem. It proves the full
correspondence with representation universe `0` from the four other global
inputs and premise 2. Premise 1 below names those four inputs. The global
inputs are now pursued over totally complex number fields. The third
theorem of the composite does the same as the second with the totally
complex forms of three of the global inputs. Up to the twenty-seventh
version it assumed in addition the published totally complex reduction
statement D (`Henniart.CandidateExistenceTCReductionStatement`); at commit
`24390f9f` that statement follows from published results (the proof of
`CandidateExistenceExactStabilizerTCReductionStatement` and a published
adapter), and the third theorem no longer assumes it. The fourth theorem
does the same as the second with Harris's Prop. 4.8 replaced by its
published exact-stabilizer form, which the original form implies, through
the proved exact-stabilizer variant of the reduction. The fifth theorem
combines the third and the fourth: the totally complex forms of three
inputs and the exact-stabilizer form of Prop. 4.8.

For the first of these inputs, Harris's Prop. 4.8, the Library has a
reduction statement, `Global.Harris.Proposition48ReductionStatement`:
fourteen named propositions together imply it. Neither the reduction nor
any of its fourteen inputs has a Library proof. On 16 November 2026 the
operator decided to restate Prop. 4.8 under an exact-stabilizer condition;
the present formulation stays open as the fallback. See premise 1 below.

On 16 November 2026 the operator also decided the program for premise 2
and for the large external inputs of the route. The decisions draw on two
operator notes, registered as literature:
`operator-numerical-llc-route-2026-11-16` (the numerical step) and
`operator-external-inputs-plan-2026-11-16` (the external inputs). This
note records the decisions under premises 1 and 2 below and in the section
"Operator decisions of 16 November 2026". The program for premise 2
includes a conditional assembly with five premises. For the fifth, input
(I4), the operator chose on 17 November 2026 a route through the
compatibility of Henniart's candidate with weak cyclic base change of
prime degree (E3) and its reduction to
`CompatibleNumericalInjectionsStatement` (premise 2 below). For statement
meanings and sources see [the specification coverage
note](llc-specification-coverage.md); this note does not restate them.

## The target

`Langlands.Correspondence.FullCorrespondenceStatement.{uF, uP, uA}`
(module `Correspondence/FullSpecification`). The universes are those of
the p-adic field, the parameter carriers and the representation carriers.

## Published: the full correspondence from the supercuspidal one

Paths below are relative to `Langlands/`.

The published theorem
`Correspondence.fullCorrespondenceStatement_of_supercuspidalCorrespondence`
(module `Correspondence/FullCorrespondenceReduction`) proves
`FullCorrespondenceStatement.{uF, uP, uA}` from
`SupercuspidalCorrespondenceStatement.{uF, uP, uA}`. It uses only the
existence part of its hypothesis. Every other ingredient is a published
proof: conditional assembly (Henniart 2002, Thm 1.5), the L-factor
characterization of assembly (Thm 1.8), supercuspidal extension (Cor.
1.6), the supercuspidal local converse theorem, the L-factor
characterization of supercuspidal classes, the multisegment head
classification, the pole-order characterization of square-integrable
classes and the uniqueness of local constants. The module's Markdown lists
them by Lean name. The published `Correspondence.fullCharacterization`
(`Correspondence/FullCharacterizationProof`) proves Henniart 2002, Cor.
1.8, on its own as well.

## Published: Henniart's construction of the supercuspidal correspondence

Published theorems prove `SupercuspidalCorrespondenceStatement.{uK, uW,
uV}`, existence and uniqueness, from hypotheses. In the full
correspondence the universes are `uK = uF`, `uW = uP` and `uV = uA`. The
fifth version of this note was based on the fourth theorem below, whose
six premises are:

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
  the eighth theorem, adapts the route of the fourth to seventh theorems
  to the supercuspidal p-adic conductor variant; see "Published: the
  two-premise entry".

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

The fifth theorem is in the Library:

- `Henniart.Extension.supercuspidalCorrespondenceHenniartRankOneInputs`
  (module `Correspondence/HenniartCorrespondenceRankOneInputs`) proves
  `SupercuspidalCorrespondenceStatement.{uK, uW, uV}` from six propositions,
  listed below. It applies `supercuspidalCorrespondenceHenniartSixInputs`
  with two of that theorem's premises discharged:
  - S2, normalized local reciprocity, by the published
    `LocalClassField.commonClosureReciprocityExistence` (module
    `ClassFieldTheory/Local/CommonClosureExistenceProof`);
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

The sixth theorem entered the Library at commit
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
  `FiniteInertiaConductorRefinementStatement F A` for every p-adic field
  `F` and every finite-dimensional complex representation `A` of its local
  Weil group, at independent field and carrier universes. Its Markdown
  explains the proof: the Artin and Swan sums of a presentation depend
  only on the dimensions of the fixed spaces of the upper ramification
  groups, and the published
  `HerbrandBridge.presentationUpperFixedComparison` identifies those fixed
  spaces for any two presentations of the same representation.

## Published: proofs of two premises

Two of the five premises of `supercuspidalCorrespondenceHenniartFiveInputs`
have Library proofs. This section numbers premises by their position in that
theorem.

- Premise 2, `∀ p K eC, LocalFactor.NonabelianSystem.Exists.{uF, uP} K eC`
  (module `LocalFactor/NonabelianSystem`), is proved by
  `LocalFactor.NonabelianSystem.exists_system` (module
  `LocalFactor/NonabelianSystemExistsProof`). For every p-adic field `F`
  and reciprocity family `e`, at independent field and representation
  universes, it applies the published specialization
  `NonabelianBrauer.exists_of_kernelCompatibilityStatement` (module
  `LocalFactor/NonabelianBrauerSystem`) to the published proof
  `NonabelianBrauer.kernelCompatibilityStatement` of Deligne's Brauer
  kernel compatibility (module `LocalFactor/NonabelianBrauerKernelProof`).
  That proof applies the published
  `ClassFieldTheory.Global.RelativeWeilGroup.localTransferReciprocity`
  (module `ClassFieldTheory/Global/LocalRelativeWeilTransferProof`).
- Premise 4, `∀ p K,
  LocalFactor.SpectralConductor.CommonClosureRankOneConductorStatement.{uF}
  K` (module `LocalFactor/SpectralConductorRankOneStatement`; Serre 1979,
  XV §2, Thm 1 and Cor. 2–3; VI §2, Prop. 5), is proved by
  `LocalFactor.SpectralConductor.commonClosureRankOneConductor` (module
  `LocalFactor/SpectralConductorRankOneProof`). The premise says that, at
  an intermediate field `L` of the common closure, the Artin sum of an
  inertia character of a finite Galois `M/L` equals the multiplicative
  conductor of the character of `L^×` attached by the supplied normalized
  reciprocity family to an agreeing character of `W_L`. The proof's
  Markdown records that it uses no unproved Library proposition; in
  particular it does not assume
  `LocalClassField.FiniteCharacterConductorTheorems` or
  `Ramification.Padic.FiniteGaloisConductorInflationStatement`. Its
  Galois-side input is the module
  `LocalFactor/Ramification/RankOneArtinSum`.

## Published: the three-premise entry

The seventh theorem is in the Library at commit `2e46b9ca`:

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

The eighth theorem is in the Library since commit `a98af0ff`:

- `Henniart.Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor`
  (module `Correspondence/HenniartSupercuspidalConductorReductionProof`)
  proves
  `Henniart.Extension.SupercuspidalCorrespondenceHenniartSupercuspidalConductorStatement.{uK,
  uW, uV}` at independent universes. That statement says that candidate
  existence (`CandidateExistenceStatement.{uK, uW, uV, uW, uK}`),
  numerical surjectivity (`NumericalSurjectivityStatement.{uK, uW, uV}`)
  and the supercuspidal p-adic conductor variant
  (`Conductor.SupercuspidalPadicConductorExponentStatement.{uK, uV}`)
  together imply `SupercuspidalCorrespondenceStatement.{uK, uW, uV}`. It
  is the three-premise statement above with its third premise replaced by
  the variant.
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
`Conductor.supercuspidalPadicConductorExponent`; see premise 3 below. So
the supercuspidal correspondence, and with it the full correspondence,
follows from candidate existence and numerical surjectivity alone. The
first theorem of the composite below checks this in Lean.

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

| # | Premise (universes of the full correspondence) | Five-premise position | Module | Status at `d6b462be` |
| --- | --- | --- | --- | --- |
| 1 | `Henniart.CandidateExistenceStatement.{uF, uP, uA, uP, uF}` (Henniart 2000, Thm 3.1 with §§3.7–3.8) | 1 | `Correspondence/HenniartStableMapStatement` | Not proved. See below; its global inputs are now pursued over totally complex number fields. |
| 2 | `Henniart.NumericalSurjectivityStatement.{uF, uP, uA}` (Henniart 1988, Thm 1.2) | 3 | `Correspondence/HenniartNumericalStatement` | Not proved. The proofs of `SupercuspidalOrbitStratumFinitenessStatement` and of the supercuspidal p-adic conductor variant, which it uses, are in the Library. It follows the operator's Option II (see premise 2 below). At `d6b462be` the statements of the units of Option II (the polar-part model, the refined strata, (LD), (I1), the twist Swan bound, the truncated Weil-side layer, (I3), the rank-bounded premise (I4), the base case and the tower lemma) are in the Library; the rank-bounded (I4) is the form that the conditional assembly and the program for (I4) use. The Artin integrality input is proved; numerical surjectivity remains open. |
| 3 (not needed) | `Conductor.ConductorExponentStatement.{uF, uA}` (Jacquet–Piatetski-Shapiro–Shalika 1981, Thm (5.1)) | 5 | `Representation/Conductor/EssentialStatement` | Not proved; not needed. The proofs of spherical cyclicity and of the normalized inverse Whittaker realization of norm-ordered unramified principal series, on which a proof would build, are in the Library; see below. The premise is the second conjunct of `Conductor.EssentialConductorStatement`. The route needs only its supercuspidal p-adic variant, which is proved; see premise 3 below. |

Premise 1. The Library states the proposition
`Henniart.CandidateExistenceReductionStatement.{uK, uW, uP, uE, uQ}`
(module `Correspondence/HenniartCandidateExistenceReductionStatement`). It
is proved: `Henniart.candidateExistenceReduction` (module
`Correspondence/HenniartCandidateExistenceReductionProof`). The statement
says that five global inputs together imply
`CandidateExistenceStatement.{uK, uW, 0, uE, uQ}`, that is, candidate
existence with the automorphic-lattice universe (the third universe
argument) equal to `0` and the other four universes arbitrary. The inputs,
at the universes of the statement, are:

1. `Global.Harris.Proposition48Statement.{uK, 0, 0, 0, uP}` (Harris 1998,
   Prop. 4.8);
2. `ClassFieldTheory.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP}`
   (Henniart 2000, Thm 2.4);
3. `ClassFieldTheory.Local.LocalRelativeClassFormationStatement.{0}`;
4. `Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement.{0, uW, uP}`
   (Henniart 2000, Lemme 2.8);
5. `Global.PoleComparison.HenniartCompositeMapStatement.{0, uK, uW, uP, uE}`
   (Henniart 2000, §3.8).

The universe `0` comes from the globalization, which produces number
fields in `Type`. The route needs candidate existence with the automorphic
universe `uA` arbitrary. The statement's Markdown leaves the passage
between these universes to the proof of candidate existence. The operator
decided on 13 November 2026 that the target, candidate existence with `uA`
arbitrary, stays unchanged. A search of the Lean sources at commit
`314cfd1a` found a proof of input 3 and of none of the others.

- The reduction itself: proved. It entered the Library at commit
  `457e31a2` on 14 November 2026. It contains `theorem
  Henniart.candidateExistenceReduction :
  CandidateExistenceReductionStatement.{uK, uW, uP, uE, uQ}`. The same
  change removed the duplicate declaration
  `Automorphic.OperatorRealization.evaluate_toContinuous_smul` that had
  blocked the proof. That theorem is now declared once, in the new module
  `Automorphic/OperatorRealizationEvaluation`. The reduction is
  conditional: its five inputs are listed below, and only input 3 has a
  Library proof.
- Input 1, Harris 1998, Prop. 4.8: no Library proof.
  - Harris's Prop. 4.8: the unchanged
    `Global.Harris.Proposition48Statement` at `.{uF, 0, 0, 0, uV}` for
    arbitrary `uF` and `uV`; `candidateExistenceReduction` uses it at
    `.{uK, 0, 0, 0, uP}`. Its proof is to be assembled from the reduction
    statement `Global.Harris.Proposition48ReductionStatement` and the
    proofs of that statement's inputs. A conditional theorem that leaves
    any of these inputs as hypotheses does not prove it.
  - The reduction statement is now in the Library (module
    `Global/Arithmetic/HarrisProposition48ReductionStatement`). It says
    that the conjunction of fourteen named propositions implies
    `Proposition48Statement.{uF, 0, 0, 0, uV}`. It has no proof at commit
    `d6b462be`. The table after this list gives its fourteen inputs.
  - The reduction statement and its fourteen inputs were stated together;
    that statement proves nothing itself. The table below lists the
    inputs. The reduction and inputs 5, 6 and 9–14 also have totally
    complex forms (statement modules H2–H4 under "Premise 1 over totally complex
    fields" below).
  - Operator decision of 16 November 2026: Harris 1998, Prop. 4.8, and its
    induction are to be restated with the exact-stabilizer condition on
    the auxiliary character (`HasExactWeilStabilizer`) in place of general
    position, as new statements; the interfaces B5, B6 and B7 are to be
    stated of the operator's plan note (Section 2.2) in the Library's
    vocabulary of weak base change; and the reduction is to be derived
    again. In the restated prime branch, B6 replaces input 8 below,
    `HarrisSupercuspidalLocalComparisonStatement` (the comparison at a
    split supercuspidal place, interface A2 of the plan note); the
    singleton branch gets B5, and both branches get B7 for the infinity
    type of the output. The present formulation, its inputs and the
    Drinfeld-tower branch behind input 8 stay open as the fallback. The
    first statements of the branch are the exact-stabilizer datum, its
    validity predicates, the restated proposition and two inheritance
    statements; the vocabulary for B6, namely towers of cyclic extensions
    of prime degree, successive weak base changes along them and terminal
    families of Hecke characters; and B5, supercuspidality descending from
    a cuspidal weak base change at a unique place, with its totally
    complex form. B5–B7 are to be proved in the trace-formula and
    base-change program for input (I3). B6 is taken as in Section 2.2 of
    the plan note, not the variant of its Remark 4.2. Its proof will need
    Arthur–Clozel, Ch. III, Thm 5.1, for representations induced from
    unitary cuspidal data along the tower, together with Thm III.4.2(c).
    Thm III.5.1 is also what the proof of (I4) under premise 2 needs.
    Further definitions and statements of the branch:
    - the vocabulary for B7, the transport of complex-place parameters and
      sums over places;
    - the vocabulary of the archimedean bridge, with complex exponents,
      shifted highest weights and Clozel regularity;
    - the cuspidal complex-place parameters and the totally complex bridge
      to infinitesimal characters;
    - the complex-place parameters of isobaric data and of Hecke families;
    - the statement that, under the published
      `CuspidalEulerConstituentRecoveryStatement`, isobaric data with a
      family of Hecke characters have the complex-place parameters of that
      family;
    - the real-place parameters of isobaric data;
    - the statements B6 and B7;
    - for (I4), the local components and the total supercuspidal support
      of isobaric data and Arthur–Clozel III.5.1 in restricted form (see
      premise 2).

    At commit `ab9053b1` the Library contains the first published parts of
    this branch, and they are definitions only.
    - Module `Global/Arithmetic/HarrisProposition48ExactStabilizerData`
      defines the datum predicate
      `Global.Harris.IsProposition48ExactStabilizerDatum` and the four
      validity predicates of the induction: `IsExactStabilizerValid`,
      `IsExactStabilizerValidAtParity`,
      `IsAuxiliaryExactStabilizerValidAtParity` and
      `IsAuxiliaryExactStabilizerValid`. Each is a published definition
      with one conjunct changed: general position of the auxiliary
      character becomes `GeneralPosition.HasExactWeilStabilizer`, or a
      called predicate is renamed accordingly. The module also proves that
      each new predicate implies its published counterpart. The restated
      proposition and the two inheritance statements were not in the
      Library at that commit (see below for commit `d26f6985`).
    - Module `Automorphic/Unramified/PrimeCyclicBaseChangeTower` gives the
      vocabulary for B6. Its structure `PrimeCyclicBaseChangeTower F K` is
      a finite increasing family of intermediate fields of `K/F`, from `⊥`
      to `⊤`, in which every step is Galois and cyclic of prime degree;
      `K/F` itself need not be Galois. It also defines `IsobaricChain`, a
      supplied family of isobaric data, one at each level, with the
      predicates `IsUnitary`, `IsSuccessiveWeakBaseChange`, `StartsAt` and
      `StartsAtCuspidal`, and the terminal datum `terminal` over `K`. By
      its Markdown, the module states no B6 implication and constructs no
      weak base change.

    On 17 November 2026 the operator ruled on three questions of design of
    this branch:
    - Bridge ruling: B7 is stated literally, and the archimedean bridge is
      a separate named premise in two parts. Its normalization is fixed
      against `ArchimedeanGL.IsRegularAlgebraicCharacter` by worked cases
      `n = 1` and `n = 2`. Its proof belongs to the archimedean part of
      the route, not to this branch.
    - Standard B6 ruling: B6 and B7 are canonical statements with no
      hypothesis of E2 or of Arthur–Clozel III.5.1 inside them. III.5.1 in
      the generality of the source is its own named premise, stated in
      this branch and listed among the unproved external inputs. The
      trace-formula and base-change program derives B6 and B7 from it
      conditionally, and nothing derived from it counts as an
      unconditional proof. The restricted route stays the intended end. So
      the prime branch is to use B6 only through one isolated lemma (claim
      (2) of Remark 4.2 of the plan note), and B7 only in a form
      restricted to classes that are supercuspidal at the auxiliary
      conjugate pair. The whole-tower variant is to be decided once the
      restricted III.5.1 is proved. The general-position formulation and
      the Drinfeld-tower fallback stay open.
    - R2 ruling: solutions of the restated induction carry their
      parameters at the complex places. The regular algebraicity of the
      induced class then comes from the restricted B7(2) and the
      children's parameters, and in the singleton branch from the
      restricted B7(1). These restricted forms assume only unitary
      cuspidal classes that are supercuspidal at the auxiliary conjugate
      pair, with no algebraicity, so they do not follow from the
      restricted III.5.1. The canonical B7 stays a published statement
      that the branches do not use, and the restated proposition is
      unchanged.

    Following these rulings, the branch states the restricted B7 and the
    restricted strong compatibility of cyclic base change with
    complex-place parameters, without algebraicity (a premise of the
    trace-formula and base-change program). It also states, with their
    totally complex forms, the complex-place parameter data of solutions,
    the distinctness of Mackey components, the two exact-stabilizer
    branches with B6 in place of A2, rank one with parameters, the
    parameter untwist and the reduction of the restated proposition. The
    parity correction, the Mackey step and the isobaric Galois invariance
    of the general-position reduction carry over unchanged; the parameter
    form of rank one replaces the rank-one starting cases, and the prime
    orbit, the singleton, the reduction and the final assembly need second
    versions. None of these statements had a module in the Library at
    commit `ab9053b1`.

    At commit `d26f6985` the Library has the following statements and
    definitions of this branch. None of the statements is proved, at that
    commit or at commit `8aede86c`.
    - B5: `CyclicWeakBaseChangeSupercuspidalStatement` and its totally
      complex form `CyclicWeakBaseChangeSupercuspidalTCStatement` (module
      `Automorphic/Unramified/CyclicWeakBaseChangeSupercuspidalStatement`).
    - Standard B6: `TowerBaseChangeHeckeComponentStatement` and
      `TowerBaseChangeHeckeComponentTCStatement` (module
      `Automorphic/Unramified/TowerBaseChangeHeckeComponentStatement`),
      and `CyclicPrimeIsobaricBaseChangeTCStatement` (module
      `Automorphic/Unramified/CyclicPrimeIsobaricBaseChangeTCStatement`).
    - B7: `CyclicWeakBaseChangeComplexPlaceStatement` and
      `CyclicWeakBaseChangeComplexPlaceTCStatement` (module
      `Automorphic/Unramified/CyclicWeakBaseChangeComplexPlaceStatement`).
      The restricted B7 is
      `RestrictedCyclicWeakBaseChangeComplexPlaceStatement` (module
      `Automorphic/Unramified/RestrictedCyclicWeakBaseChangeComplexPlaceStatement`).
      It has no separate totally complex form.
    - The statement on isobaric data with a family of Hecke characters:
      `IsobaricHeckeComplexPlaceParameterStatement` (module
      `Automorphic/Unramified/IsobaricHeckeComplexPlaceParameterStatement`).
      By its Markdown it is a separate branch premise, not a base-change
      statement.
    - The restated proposition:
      `Global.Harris.Proposition48ExactStabilizerStatement` (module
      `Global/Arithmetic/HarrisProposition48ExactStabilizerStatement`).
      The same module proves
      `proposition48ExactStabilizerStatement_of_proposition48Statement`:
      the published general-position `Proposition48Statement` implies the
      restated proposition, because the exact-stabilizer datum implies the
      general-position datum. The two inheritance statements,
      `Proposition48ExactStabilizerMackeyInheritanceStatement` and
      `Proposition48ExactStabilizerParityInheritanceStatement`, are in
      module
      `Global/Arithmetic/HarrisProposition48ExactStabilizerInheritanceStatement`.
      Both are proved at commit `f050c0b1`:
      `proposition48ExactStabilizerMackeyInheritance` (module
      `Global/Arithmetic/HarrisProposition48ExactStabilizerMackeyProof`)
      and `proposition48ExactStabilizerParityInheritance` (module
      `Global/Arithmetic/HarrisProposition48ExactStabilizerParityInheritanceProof`).
    - Module
      `Global/Arithmetic/HarrisProposition48ExactStabilizerParameterData`
      defines, and asserts nothing about, the vocabulary for the
      complex-place parameter data of solutions and the distinctness of
      Mackey components: `IsInducedComplexPlaceParameter`,
      `HasInducedComplexPlaceParameters`, `HasParameterSolution`,
      `IsMackeyConstituent` and `HasDistinctMackeyComponents`.
    - Already at commit `ab9053b1` the Library proves
      `Global.generalPositionOfExactStabilizer :
      GeneralPositionOfExactStabilizerStatement.{uF}` (module
      `Global/Arithmetic/GeneralPositionOfExactStabilizerProof`): Harris's
      condition (4.12) implies general position.

    The Henniart consumers of the restated proposition are stated in three
    modules. They were not in the Library at commit `d26f6985`; all three
    are at commit `8aede86c`:
    - Module
      `Global/Arithmetic/HenniartHarrisDatumExactStabilizerStatement`:
      `Global.HarrisDatumCharacterRealizationExactStabilizerStatement`,
      Henniart's datum characters of §3.6, Lemme 3, with the exact Weil
      stabilizer of the auxiliary character;
    - Module
      `Global/Arithmetic/HenniartGlobalizationExactStabilizerStatement`:
      `Global.HenniartGlobalizationExactStabilizerStatement` (the restated
      proposition implies `RelativeGaloisGlobalization`) and the
      corresponding reduction statement
      `Global.HenniartGlobalizationExactStabilizerReductionStatement`;
    - Module
      `Correspondence/HenniartCandidateExistenceExactStabilizerReductionStatement`:
      `Henniart.CandidateExistenceExactStabilizerReductionStatement` (the
      restated proposition and four further premises imply
      `CandidateExistenceStatement`) and its totally complex form
      `Henniart.CandidateExistenceExactStabilizerTCReductionStatement`. At
      commit `8aede86c` these five propositions were unproved, and no
      other Library module named them. Each module also proves that each
      of its new statements implies the corresponding published statement:
      the datum module because every exact-stabilizer datum is a datum
      (`IsProposition48ExactStabilizerDatum.isProposition48Datum`), the
      other two through
      `proposition48ExactStabilizerStatement_of_proposition48Statement`.
      At commit `f050c0b1` the datum statement and the two reduction
      statements are proved:
    - `Global.harrisDatumCharacterRealizationExactStabilizer` (module
      `Global/Arithmetic/HenniartHarrisDatumExactStabilizerProof`);
    - `Global.henniartGlobalizationExactStabilizerReduction` (module
      `Global/Arithmetic/HenniartGlobalizationExactStabilizerProof`);
    - `Henniart.candidateExistenceExactStabilizerReduction` (module
      `Correspondence/HenniartCandidateExistenceExactStabilizerReductionProof`).
      By its Markdown it follows the assembly of the published
      `candidateExistenceReduction`, with the exact-stabilizer
      globalization reduction in place of the published one. So
      `CandidateExistenceStatement.{uK, uW, 0, uE, uQ}` follows from the
      restated proposition, Thm 2.4, the local class formation (proved),
      Lemme 2.8 and §3.8, that is, from inputs 2 to 5 of the published
      reduction with input 1 replaced by the restated proposition. The
      fourth theorem of the composite (section "The composite") applies
      this reduction. At commit `24390f9f` its totally complex form is
      proved: `Henniart.candidateExistenceExactStabilizerTCReduction :
      CandidateExistenceExactStabilizerTCReductionStatement` (module
      `Correspondence/HenniartCandidateExistenceExactStabilizerTCReductionProof`).
      It uses the supporting module
      `Global/Arithmetic/HenniartGlobalizationExactStabilizerTC`, which
      defines `Global.RelativeGaloisGlobalizationTC` (the relative
      globalization with a totally complex global base) and proves it from
      the exact-stabilizer datum realization, the restated proposition,
      the totally complex form of Thm 2.4 and published local and global
      facts (`henniartGlobalizationExactStabilizerTC_of_inputs`). The
      published adapter
      `candidateExistenceTCReductionStatement_of_exactStabilizer` (module
      `Correspondence/HenniartCandidateExistenceExactStabilizerReductionStatement`)
      derives the published totally complex reduction statement
      `CandidateExistenceTCReductionStatement` (D) from it; so that
      statement follows from published results, and the third theorem of
      the composite uses this derivation.
      `HenniartGlobalizationExactStabilizerStatement` (over a general
      number field) is unproved at commit `24390f9f`.

    The following statements of the restated induction are in the Library.
    The main reduction statement is described after the list of the
    statements for the two branches below.
    - At commit `ba9d1e9a`, module
      `Global/Arithmetic/HarrisProposition48ExactStabilizerDistinctnessStatement`:
      `Proposition48ExactStabilizerDistinctnessStatement` and its totally
      complex form `Proposition48ExactStabilizerDistinctnessTCStatement`.
      The first has three premises: B6, the tower comparison of Hecke
      components (`TowerBaseChangeHeckeComponentStatement`); Arthur–Clozel
      III.4.2(c), prime cyclic base change of unitary isobaric data
      (`CyclicPrimeIsobaricBaseChangeStatement`, module
      `Automorphic/Unramified/IsobaricCyclicTransferStatement`); and
      spectral rigidity (`CuspidalSpectralRigidityStatement`). From them it
      derives `HasDistinctMackeyComponents D` for every problem with
      exact-stabilizer validity and every prime cyclic step `D` with `[D :
      E]` Mackey classes (`Nat.card (Q.MackeyIndex D) = Module.finrank Q.E
      D`). This cardinality hypothesis selects the prime-orbit case of
      Harris's induction, as opposed to the singleton case of the same
      prime-degree step. The totally complex form takes the totally complex
      forms of the three premises (`TowerBaseChangeHeckeComponentTCStatement`,
      `CyclicPrimeIsobaricBaseChangeTCStatement` and
      `CuspidalSpectralRigidityTCStatement`), with the same hypotheses on
      the problem and the step and the same conclusion.
    - At commit `ba9d1e9a`, module
      `Global/Arithmetic/HarrisProposition48ExactStabilizerParameterAuxiliaryStatement`:
      `Proposition48ExactStabilizerAuxiliaryRankOneStatement` (rank one
      with parameters) and `Proposition48ExactStabilizerParameterUntwistStatement`.
    - At commit `f050c0b1`, module
      `Global/Arithmetic/HarrisProposition48ExactStabilizerBranchStatement`:
      the prime-orbit and singleton branches under the exact-stabilizer
      condition, `Proposition48ExactStabilizerPrimeBranchStatement` and
      `Proposition48ExactStabilizerSingletonBranchStatement`, with their
      totally complex forms. By its declarations and its Markdown, each is
      the published general-position branch (modules
      `Global/Arithmetic/HarrisProposition48PrimeBranchStatement` and
      `HarrisProposition48SingletonBranchStatement`) with the following
      changes. Both branches use the exact-stabilizer validity predicates
      and the induced complex-place parameters of the children
      (`HasInducedComplexPlaceParameters`) and of the solution
      (`HasParameterSolution`). Both branches add two premises: the
      restricted B7
      (`RestrictedCyclicWeakBaseChangeComplexPlaceStatement`) and the
      archimedean bridge (`CuspidalComplexParameterBridgeTCStatement`);
      their totally complex forms keep these two premises unchanged. The
      prime branch drops the premise A2
      (`HarrisSupercuspidalLocalComparisonStatement`) and assumes
      `HasDistinctMackeyComponents D`; like the published prime branch, it
      assumes `[D : E]` Mackey classes. The singleton branch (one Mackey
      class) also adds B5, `CyclicWeakBaseChangeSupercuspidalStatement`,
      after `CyclicStableDescentStatement`; its totally complex form takes
      `CyclicWeakBaseChangeSupercuspidalTCStatement`. By the module's
      Markdown, B5 supplies what no published premise of the singleton
      branch says at the auxiliary place: the selected descent is
      supercuspidal there, because its base change, the child's
      constituent, has a supercuspidal component. The module
      `Global/Arithmetic/HarrisProposition48StabilizerComparison` (commit
      `f050c0b1`) proves `PlaceDatum.exactWeilStabilizer_iff_global`,
      which reads the local exact-stabilizer condition on the number
      field. The two branches are reduced to named inputs, stated as
      follows:
    - three statements at the auxiliary conjugate pair, used by both
      branches, in module
      `Global/Arithmetic/HarrisAuxiliaryConjugatePairStatement` (unitary
      central character and supercuspidality at the conjugate place from
      conjugate self-duality, and that places above a split prime differ
      from their conjugates);
    - eight Mackey-step statements (Mackey fibres, Galois conjugate
      constituents, child transport, parameter and induction stages,
      regular algebraicity, and conjugate self-duality after weak
      induction with its totally complex form) in module
      `Global/Arithmetic/HarrisProposition48MackeyTransportStatement`, and
      three statements in module
      `Automorphic/CuspidalArithmeticTransportStatement`: arithmetic
      pullback of cuspidal realizations along a ring isomorphism of number
      fields (`arithmeticComap`) preserves a unitary central character and
      a supercuspidal component, and, for CM fields, conjugate
      self-duality;
    - four statements for the singleton branch (Galois stability of the
      Mackey constituent, unitarity under weak base change, the singleton
      parameter identity and the selection of a descent by Harris's Lemma
      1.6) in module
      `Global/Arithmetic/HarrisProposition48SingletonDescentStatement`;
    - the reduction of the prime branch and of its totally complex form to
      twelve named inputs, which are the statements of the first two items
      above, in module
      `Global/Arithmetic/HarrisProposition48ExactStabilizerPrimeBranchReductionStatement`.
      The statement modules of those two items entered the Library at
      `95d37e11`; the reduction module was not in the Library at
      `d6b462be`. The four singleton inputs of the third item were
      published at `6e9e589b`; these are statements, not proofs of the
      branch. The module
      `Global/Arithmetic/HarrisProposition48SingletonBranchReductionStatement`
      concerns the older general-position singleton branch and its totally
      complex form, not the exact-stabilizer branch.

    Rank one and the parameter untwist have exact proofs in the Library,
    both at `95d37e11`:
    `Global.Harris.proposition48ExactStabilizerAuxiliaryRankOne` (module
    `Global/Arithmetic/HarrisProposition48ExactStabilizerAuxiliaryRankOneProof`)
    and `Global.Harris.proposition48ExactStabilizerParameterUntwist`
    (module
    `Global/Arithmetic/HarrisProposition48ExactStabilizerParameterUntwistProof`).
    Both retain the independent universes `uF`, `uV` without additional
    hypotheses. The first uses the degree-one Hecke realization on `GL₁`
    and the induced parameter at each complex place. The second multiplies
    each block by the parameter of the inverse correction character; this
    agrees with twisting by the norm parameter before taking the Langlands
    sum. They discharge inputs 1 and 4 below, respectively.

    The Library has a conditional reduction for distinctness in
    `Global/Arithmetic/HarrisProposition48ExactStabilizerDistinctnessReduction`
    (commit `95d37e11`). Theorems
    `Global.Harris.proposition48ExactStabilizerDistinctnessReduction` and
    `Global.Harris.proposition48ExactStabilizerDistinctnessTCReduction`
    give the two distinctness statements from
    `Automorphic.CuspidalArithmeticSpectralTransportStatement.{0, 0, uV}`
    (module `Automorphic/CuspidalArithmeticSpectralTransportStatement`).
    B6 and Arthur–Clozel III.4.2(c), or their totally complex forms, are
    already hypotheses of the respective target, and these proofs do not
    use its rigidity hypothesis. At `d6b462be` the added transport premise
    is proved at arbitrary `uK`, `uL`, `uV` by
    `Automorphic.cuspidalArithmeticSpectralTransport` (module
    `Automorphic/CuspidalArithmeticSpectralTransportProof`). Applying each
    published reduction to that theorem checks at `.{uF, uV}` with zero
    errors and warnings in a separate Lean check. Thus both forms of input
    8 follow from published results, though neither has a named exact
    proof in this snapshot. The B6 and III.4.2(c) hypotheses inside those
    targets are not discharged by the transport proof.

    The reduction statement of the restated induction is in the Library at
    commit `24390f9f` (module
    `Global/Arithmetic/HarrisProposition48ExactStabilizerReductionStatement`,
    namespace `Global.Harris`).
    `Proposition48ExactStabilizerReductionStatement.{uF, uV}` states,
    without proof, that a conjunction of 22 named statements implies
    `Proposition48ExactStabilizerStatement.{uF, 0, 0, 0, uV}`, the
    restated proposition at the universes used by globalization. By its
    Markdown the 22 inputs are, in order: the auxiliary rank-one statement
    with parameters (proved); the published parity normalization and
    parity untwist statements; the parameter untwist statement (proved);
    the published Mackey step; the Mackey and parity inheritance
    statements (both proved, see above); distinctness; the prime and
    singleton branches; A1 (Harris's Thm 1.2 for cuspidal data); spectral
    rigidity C2; isobaric invariance; B2, B3, B1, B4, B5 and B6;
    Arthur–Clozel III.4.2(c); the restricted B7; and the archimedean
    bridge `CuspidalComplexParameterBridgeTCStatement`. Compared with the
    published `Proposition48ReductionStatement`, the comparison A2 at a
    split supercuspidal place is dropped and the canonical B7 is not an
    input. `Proposition48ExactStabilizerReductionTCStatement.{uF, uV}` has
    the same 22 positions with the totally complex forms at positions 8–10
    and 12–20, and the same conclusion. Neither reduction nor the
    exact-stabilizer form of Proposition 4.8 is proved at `d6b462be`. In
    addition to the established proofs at positions 1, 4, 6 and 7 and the
    composable input 8, the Library now proves the following:

    | Input | Theorem | Declaration-site module |
    | --- | --- | --- |
    | 5, Mackey step | `Global.Harris.proposition48MackeyStep` | `Global/Arithmetic/HarrisProposition48MackeyStepProof` |
    | 13, isobaric invariance | `Global.Harris.proposition48IsobaricInvariance` | `Global/Arithmetic/HarrisProposition48IsobaricInvarianceProof` |
    | 13, totally complex | `Global.Harris.proposition48IsobaricInvarianceTC` | `Global/Arithmetic/HarrisProposition48IsobaricInvarianceTCProof` |
    | 22, archimedean bridge | `Automorphic.cuspidalComplexParameterBridgeTC` | `Automorphic/CuspidalComplexParameterBridgeProof` |

    The bridge uses the totally complex A1 proof. None of these theorems
    proves the two branch inputs or Harris's Proposition 4.8.
  - A further use of Prop. 4.8 is the statement that Harris's Prop. 4.8
    implies `HenniartGlobalizationStatement`.
- Input 2, Henniart 2000, Thm 2.4: Henniart's local induction from unitary
  supercuspidals for associated pairs. A proof attempt established the
  statement only under three added hypotheses: `AssociatedGammaStatement`,
  the exhaustion of unitary generic representations, and
  `NonabelianSystem.Exists`. The input needs a proof without added
  hypotheses. At commit `314cfd1a` two of the three hypotheses are proved,
  and only `AssociatedGammaStatement` is open.
  - `LocalFactor.NonabelianSystem.Exists` is proved by
    `NonabelianSystem.exists_system`; see premise 2 of the five-premise
    theorem above.
  - `ClassFieldTheory.Global.RelativeWeilGroup.AssociatedGammaStatement`
    (module `Automorphic/AssociatedFactorStatement`) has no Library proof.
    The published `RelativeWeilGroup.associatedGamma_of_inputs` (module
    `Automorphic/AssociatedGammaFinal`) derives
    `AssociatedGammaStatement.{u, uV, uP, uQ, uE}` from two propositions:
    `Global.CuspidalPairGlobalFunctionalEquationStatement.{u, u}` (module
    `Global/Factors/CuspidalPairFunctionalEquationStatement`) and
    `StableTwistPairGammaMatchStatement.{u, uV, uE}`. The second is proved
    by `RelativeWeilGroup.stableTwistPairGammaMatchStatement` (module
    `Automorphic/StableTwistGammaMatchProof`). So the gamma statement
    follows from the global Rankin–Selberg functional equation for
    cuspidal pairs alone. A separate Lean check (theorem
    `associatedGamma_of_globalFE_check`, not in the Library) composes the
    two published theorems. It compiles at commit `544dba09` with 0 errors
    and 0 warnings and uses only the axioms `propext`, `Classical.choice`
    and `Quot.sound`. The functional equation has no Library proof.
  - The exhaustion of unitary generic representations,
    `Classification.UnitaryGenericExhaustion F T` (module
    `Representation/Classification/UnitaryGenericStatement`), is proved,
    since the nineteenth version, by
    `Classification.unitaryGenericExhaustion` (module
    `Representation/Classification/UnitaryGenericExhaustionProof`), for
    every p-adic field `F` and every `T`, at independent universes. It
    applies the published
    `Classification.unitaryGenericExhaustion_of_tadicUnitaryDualExhaustion`
    (module
    `Representation/Classification/UnitaryGenericExhaustionReduction`) to
    `Classification.tadicUnitaryDualExhaustion` (module
    `Representation/Classification/TadicUnitaryDualExhaustionProof`),
    which proves Tadić's exhaustion of the unitary dual,
    `Classification.TadicUnitaryDualExhaustion F T`, with no hypotheses.
    That proof supplies the published reduction `tadicExhaustionReduction`
    with proofs of Tadić's lemma statements, of the unitarizability of
    Speh representations (`spehUnitarizability`) and of the multisegment
    head classification. So the planned proof of the totally complex form
    of Thm 2.4 (statement B3 below) now needs only that of
    `AssociatedGammaStatement` (statement B1).
- Input 3, local relative class formation: proved. The Library proves it:
  `ClassFieldTheory.Local.localRelativeClassFormation` (module
  `ClassFieldTheory/Local/LocalRelativeClassFormationProof`). It proves
  `LocalRelativeClassFormationStatement.{u}` at every universe `u`. The
  proof keeps the invariant family of the published
  `ClassFieldTheory.Local.localAbsoluteCorestrictionCompatibleClassFormation`
  and drops six of its fifteen conjuncts.
- Input 4, Henniart 2000, Lemme 2.8:
  `RelativeCertifiedPoleComparisonsStatement`; this note records no proof
  of it.
- Input 5, Henniart 2000, §3.8: `HenniartCompositeMapStatement`, to be
  proved by combining four published propositions. Three of them have
  Library proofs at commit `544dba09`:
  `Global.PoleComparison.relativeIsometryOperation` proves
  `RelativeIsometryOperationStatement` (module
  `Global/Factors/RelativeIsometryOperationProof`);
  `Global.PoleComparison.henniartCompositeOperation` proves
  `HenniartCompositeOperationStatement` (module
  `Global/Factors/HenniartCompositeOperationProof`); and
  `Global.PoleComparison.henniartCompositeFactor` proves
  `HenniartCompositeFactorStatement` (module
  `Global/Factors/HenniartCompositeFactorProof`). The fourth,
  `Global.PoleComparison.RelativeIsometryFactorStatement` (compatibility
  of the generated isometry with determinants and with pair L- and
  ε-factors), has no Library proof.
- The candidate-existence reduction statement and the statements of Lemme
  2.8 and §3.8 belong to the formalization of Henniart's global
  construction (Henniart 2000, §3).

The fourteen inputs of `Global.Harris.Proposition48ReductionStatement`, in
their Lean order, follow. The universes are those at which the reduction
uses them. Modules are relative to `Langlands/`. The names are in the
namespaces `Langlands.Global.Harris` (rows 1–6 and 10),
`Langlands.GaloisRepresentation` (rows 7 and 8) and
`Langlands.Automorphic.Unramified` (rows 9 and 11–14). The descriptions
paraphrase the docstrings and Markdown of the statements. None of the
fourteen has a Library proof at commit `314cfd1a`.

| # | Input statement (universes in the reduction) | Module | Content |
| --- | --- | --- | --- |
| 1 | `Proposition48AuxiliaryRankOneStatement.{uF, uV}` | `Global/Arithmetic/HarrisProposition48AuxiliaryInputStatement` | Base case `[E' : E] = 1` of the one-place induction: realization by a Hecke character, using only the auxiliary place |
| 2 | `Proposition48AuxiliaryParityNormalizationStatement.{uF}` | same module | Correction of the inherited infinity parity by a conjugate-inverse Hecke character of the base field |
| 3 | `Proposition48AuxiliaryParityUntwistStatement.{uF, uV}` | same module | Undoing that correction on a supplied solution of the corrected problem |
| 4 | `Proposition48MackeyStepStatement.{uF}` | `Global/Arithmetic/HarrisProposition48MackeyStepStatement` | One prime cyclic Mackey step with all its children, of smaller normal-closure degree and inherited parity |
| 5 | `Proposition48PrimeBranchStatement.{uF, uV}` | `Global/Arithmetic/HarrisProposition48PrimeBranchStatement` | Assembly of the Mackey constituents of a prime orbit |
| 6 | `Proposition48SingletonBranchStatement.{uF, uV}` | `Global/Arithmetic/HarrisProposition48SingletonBranchStatement` | Cyclic descent of a singleton Mackey constituent (Harris 1998, Lemma 1.6) |
| 7 | `Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV}` | `Galois/Harris1998ExistenceStatement` | Cuspidal case of Harris 1998, Thm 1.2 |
| 8 | `HarrisSupercuspidalLocalComparisonStatement.{0, 0, uV, uV}` | `Galois/HarrisSupercuspidalLocalComparisonStatement` | Equal supercuspidal components at a split place give isomorphic local Galois restrictions (derived from Harris 1999, Thm 5.9(ii)); in the restated exact-stabilizer prime branch, B6 takes its place |
| 9 | `CuspidalSpectralRigidityStatement.{0, uV}` | `Automorphic/Unramified/CuspidalSpectralRigidityStatement` | Mixed-rank cuspidal spectral rigidity |
| 10 | `Proposition48IsobaricInvarianceStatement.{uV}` | `Global/Arithmetic/HarrisProposition48IsobaricInvarianceStatement` | Galois invariance of the isobaric multiset from equal Euler systems |
| 11 | `CyclicRegularInductionStatement.{0, 0, uV, uV}` | `Automorphic/Unramified/CyclicTransferStatement` | Arthur–Clozel, Lemma III.6.4 with Thm III.6.2, in weak-induction form |
| 12 | `CyclicRegularOrbitLiftStatement.{0, 0, uV, uV}` | `Automorphic/Unramified/IsobaricCyclicTransferStatement` | Arthur–Clozel, Lemma III.6.4, in base-change form |
| 13 | `CyclicStableDescentStatement.{0, 0, uV, uV}` | `Automorphic/Unramified/CyclicTransferStatement` | Arthur–Clozel, Lemma III.6.3 |
| 14 | `CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV}` | `Automorphic/Unramified/CyclicWeakInductionSupercuspidalStatement` | Supercuspidality at a place of a cyclic weak induction (derived from Henniart–Herb 1995, Prop. 5.5) |

The trace-formula and base-change program for input (I3) (premise 2 below)
includes, among other results, local automorphic induction at a non-split
place (B4) and the statements B5–B7 of the exact-stabilizer branch. The
earlier published statement `Global.Harris.Proposition48RankOneStatement`
(module `Global/Arithmetic/HarrisProposition48RankOneStatement`; every
valid problem with `[E' : E] = 1` has a solution) is not one of the
fourteen inputs. Input 1 is the corresponding base case under the
one-place hypotheses `IsAuxiliaryValid` of the internal induction, which
impose no condition at the primary place. The structure
`Global.Harris.Proposition48Problem` (module
`Global/Arithmetic/HarrisProposition48InductionData`) bundles the data of
one instance of `Proposition48Statement`, with the number fields in
`Type`; the statement's Markdown describes how the induction uses it.

The transport of supercuspidal unitary lattices between carrier universes,
which the globalization in universe 0 makes necessary, is needed by a
proof of candidate existence at arbitrary universes. The second to fifth
theorems of the composite below avoid this transport: they fix the
representation universe of the full correspondence at `0`.

Premise 1 over totally complex fields. Henniart's globalization (Théorème
2.4 and §3) works with CM number fields and their finite extensions, which
are totally complex. So the global inputs of the reduction are needed only
over totally complex number fields. On 15 November 2026 the operator made
this the route (Option A). It takes the archimedean theory of GL_n(R) off
the critical path; the work on GL_n(R) continues. Five statement modules
were added; each states published propositions with
`[NumberField.IsTotallyComplex F]` inserted after `[NumberField F]`, at
the same universes, the rest unchanged, in a new module. The names end in
`TCStatement`. All five are in the Library at commit `314cfd1a`, with the
content below.

| Label | Module | Propositions |
| --- | --- | --- |
| A | `Global/Factors/CuspidalPairFunctionalEquationTCStatement` | `Global.CuspidalArchimedeanParameterExistenceTCStatement`, `Global.CuspidalPairCompletedEquationTCStatement`, `Global.CuspidalPairGlobalFunctionalEquationTCStatement` |
| B | `Automorphic/AssociatedFactorTCStatement` | `RelativeWeilGroup.AssociatedGammaTCStatement` (Thm 2.3), `AssociatedTemperedFactorTCStatement` (Cor. 2.3), `AssociatedSupercuspidalInductionTCStatement` (Thm 2.4), `AssociatedCuspidalFactorTCStatement` (Cor. 2.4) |
| C | `Global/Factors/PoleComparisonTCStatement` | `PoleComparison.RelativeCertifiedPoleComparisonsTCStatement` (Lemme 2.8), `RelativeIsometryFactorTCStatement`, `HenniartCompositeMapTCStatement` (§3.8) |
| D | `Correspondence/HenniartCandidateExistenceTCReductionStatement` | `Henniart.CandidateExistenceTCReductionStatement`: `CandidateExistenceReductionStatement` with inputs 2, 4 and 5 replaced by their totally complex forms; inputs 1 (Harris) and 3 unchanged |
| L | `Automorphic/AssociatedFactorTCReductionStatement` | the totally complex forms of three published links: `Global.CuspidalPairFunctionalEquationReductionTCStatement` (local data, A1 and A2 give A3), `RelativeWeilGroup.AssociatedGammaReductionTCStatement` (A3 at `.{u, u}` gives B1; the other input of `associatedGamma_of_inputs` is proved), `RelativeWeilGroup.AssociatedCuspidalFactorReductionTCStatement` (B3 and B2 give B4) |

A separate Lean check, not in the Library, proves that each published
proposition implies its totally complex form and that D's conclusion
follows from the published `CandidateExistenceReductionStatement`, with 0
errors. It also proves links 1 and 3 from the published proofs. Each module
compiled with 0 errors and 0 warnings.

The unrestricted targets stay unchanged; their totally complex forms are
to be proved beside them. The table gives, for each totally complex form,
the planned proof and its open input as of 15 November 2026; the rows of
A1 and A2 add the Library modules published since.

| Totally complex form | Planned proof and its open input |
| --- | --- |
| A1 archimedean parameters | The planned proof needs only `ComplexGenericStandardParameterStatement`, not the GL_n(R) input. At commit `ba9d1e9a` that input is proved: `Archimedean.complexGenericStandardParameter` (module `Representation/Archimedean/ComplexGenericStandardParameterProof`). At commit `7e12a30c` the totally complex form of A1 is proved twice, both times without added hypotheses: `Global.cuspidalArchimedeanParameterExistenceTC` (module `Global/Factors/CuspidalArchimedeanParameterExistenceTCProof`) and `Automorphic.cuspidalArchimedeanParameterExistenceTC` (module `Automorphic/CuspidalArchimedeanParameterExistenceTC`), each of type `Global.CuspidalArchimedeanParameterExistenceTCStatement.{u}`. The declaration names differ, so the two modules do not clash; the first is meant as the canonical proof and the second as a duplicate that may be removed. The unrestricted A1 stays open. Two of the three premises of link 1 are proved: the local data (`Global.cuspidalPairLocalData`, module `Global/Factors/CuspidalPairLocalDataProof`) and the totally complex A1. Link 1 itself is now proved, so the totally complex A3 needs only the totally complex A2. |
| A2 completed equation | All eight unrestricted global inputs of the totally complex (G') are proved; the two totally complex semi-local equations remain. The [A2 chain](#a2-the-totally-complex-completed-rankinselberg-equation) below gives their retained premises. |
| A3 global functional equation | From the proofs of A1 and A2 and `cuspidalPairLocalData`. |
| B1 Thm 2.3 | No planned proof recorded. |
| B2 Cor. 2.3 | From B1; a proof from B1 compiles in a separate check, not in the Library. |
| B3 Thm 2.4 | From B1 and `UnitaryGenericExhaustion`. |
| B4 Cor. 2.4 | Planned; no open input recorded. |
| C1 Lemme 2.8 | A reduction from B4 compiles in a separate check, not in the Library. |
| C2 isometry factors | From B4 and B3. |
| C3 composite map | No planned proof recorded. |

### A2: the totally complex completed Rankin–Selberg equation

The chain here is for `Global.CuspidalPairCompletedEquationTCStatement`.
Module paths below with no directory are under `Global/RankinSelberg/`;
the archimedean and semi-local results are in namespace
`Langlands.Global.RankinSelbergGlobal`. The mathematical sources are
Cogdell (2004), proof of Theorem 4.1, printed pp. 219–220, for the global
argument, and Jacquet (2009), Theorem 2.1, for the complex local equations.
The Lean glue uses the separate scopes of the published statements.

**From the semi-local equations to A2.** The Library states
`Global.CuspidalPairPartialGammaEquationTCStatement`, the totally complex
(G'), in `Global/Factors/CuspidalPairPartialGammaEquationTCStatement`, and
`UnequalSemilocalEquationTCStatement` and
`EqualSemilocalEquationTCStatement` in `SemilocalEquationTCStatements`.
The theorem `Global.cuspidalPairPartialGammaGlobalTCReduction` (module
`Global/Factors/CuspidalPairPartialGammaGlobalTCReduction`) takes those
two semi-local equations and eight unrestricted premises. All eight have
published proofs. The table gives the proofs actually supplied below.

| Input | Unequal rank (theorem; module) | Equal rank (theorem; module) |
| --- | --- | --- |
| Global analytic theorem | `UnequalAnalytic.unequalAnalyticStatement_proof`; `UnequalAnalyticProof` | `EqualAnalytic.equalAnalyticStatement_proof`; `EqualAnalyticProof` |
| Unfolding | `unequalUnfoldingStatement_proof`; `UnequalUnfoldingProof` | `equalUnfoldingStatement_proof`; `EqualUnfoldingProof` |
| Euler factorization | `unequalEulerFactorization`; `UnequalEulerFactorizationProof` | `equalEulerFactorization`; `EqualEulerFactorizationProof` |
| Dual Euler factorization | `unequalDualEulerFactorization`; `UnequalDualEulerFactorizationProof` | `equalDualEulerFactorization`; `EqualDualEulerFactorizationProof` |

The Library has `Global.cuspidalPairPartialGammaTCReduction` (module
`Global/Factors/CuspidalPairPartialGammaTCReduction`): the totally complex
(G') implies A2. For unequal ranks, the published
`unequalSemilocalComplexReduction` (module
`UnequalSemilocalArchimedeanReduction`) gives the semi-local equation from
`ComplexSemilocalTheoryStatement` (module
`ArchimedeanSemilocalTheoryStatement`). For equal ranks, the published
`equalSemilocalFactorizationReductionTC` (module
`EqualSemilocalFactorizationReductionTC`) gives
`EqualSemilocalFactorizationTCStatement`, from which
`equalSemilocalReductionTC` gives the equation (both declared in
`EqualSemilocalReductionTC`). The equal-rank reduction takes the
equal-rank complex functional equation, unrestricted equal-rank
factorization and the central sign. The sign for both ranks is proved by
`archimedeanCentralSign` (module `ArchimedeanCentralSignProof`).

**Complex local functional equations.** The complex local functional
equation is `ComplexPlaceFunctionalEquationStatement` (module
`ArchimedeanFunctionalEquationStatement`). The published
`complexPlaceFunctionalEquationLocalFEReduction` (module
`ComplexPlaceFunctionalEquationLocalFEReduction`) supplies it from
`ComplexLocalUnequalFunctionalEquationStatement` and
`ComplexLocalEqualFunctionalEquationStatement` (both declared in
`ComplexPlaceFunctionalEquationReduction`). Neither all-ranks equation has
a published proof at this snapshot. `complexLocalUnequalFromNormalized`
(module `ComplexLocalUnequalFromNormalized`) reduces the unequal-rank one
to `ComplexUnequalNormalizedIntertwinerEquationStatement` (declared in
`ComplexUnequalAnalyticReduction`). On the equal-rank side,
`complexLocalEqualConvergenceReduction` (module
`ComplexLocalEqualConvergenceReduction`) reduces to growth, primal
continuation and the meromorphic equation. In module
`ComplexLocalEqualMeromorphicReduction`, the proof
`complexLocalWhittakerUniformGrowth` supplies that growth input, and
`complexLocalEqualMeromorphicReduction` reduces the all-ranks statement to
`ComplexLocalEqualPrimalContinuationStatement` (declared in
`ComplexLocalEqualConvergenceReduction`) and
`ComplexLocalEqualMeromorphicEquationStatement` (declared in
`ComplexLocalEqualDualityReduction`). Rank index zero is proved
separately: `complexLocalEqualRankZero` (module
`ComplexLocalEqualRankZero`) uses `complexLocalEqualAtRankStatement_zero`
(module `ComplexLocalEqualRankZeroReduction`) and the complex Tate theorem
(module `LocalFactor/Archimedean/ComplexTateProof`). It covers only
`GL₁(ℂ) × GL₁(ℂ)`.

**Factorization and the real-place scope.** The unrestricted factorization
is `ArchimedeanFactorizationStatement` (module
`ArchimedeanFactorizationStatement`).
`archimedeanFactorizationFromPointwise` (module
`ArchimedeanFactorizationConditional`) proves it from the unequal and
equal pointwise factorizations. The two measure premises of the older
reduction are supplied by the published `UnipotentClassProductProof` and
`RectangleTateProof`. The pointwise statements are declared in
`ArchimedeanFactorizationReduction` and
`EqualArchimedeanFactorizationReduction`, respectively. For equal ranks
`equalPointwiseOfInfiniteTests` (module `EqualInfiniteWhittakerReduction`)
obtains the pointwise statement from
`EqualInfiniteWhittakerTestStatement`. The new
`equalInfiniteWhittakerTest_of_local` (module
`EqualInfiniteWhittakerSliceReduction`) proves that premise from
`InfiniteWhittakerSliceModelStatement` (declared there) and
`RealEqualPlaceTestsStatement` and `ComplexEqualPlaceTestsStatement` (both
in `EqualInfinitePlaceTests`). The test premise includes a product of
normalized infinite Whittaker slices and nonvanishing for both the primal
and dual archimedean products.

The semi-local reductions above drop the **real local functional
equation**. They do not restrict the **factorization hypotheses** to
totally complex fields: `ComplexSemilocalTheoryStatement` still uses
unrestricted `ArchimedeanFactorizationStatement`, and
`EqualSemilocalFactorizationReductionTCStatement` still uses unrestricted
`EqualArchimedeanFactorizationStatement`. Both factorization statements
quantify over all number fields with the stated hypotheses. In particular
one cannot drop the real-place tests from the current equal-rank slice
reduction of that unrestricted target. The equal-rank semi-local proof
uses its factorization hypothesis only at the totally complex field in its
conclusion. A fieldwise factorization interface and companions of the
semi-local consumers would let a proof use the absence of real places at
that field without changing `ArchimedeanFactorizationStatement`. That is a
possible refinement, not a published reduction at this snapshot.

**Lean development check (conditional).** The following module composes
the published results. The first theorem uses the four open inputs named
above (two pointwise factorizations and two complex local functional
equations). The second replaces the equal-rank pointwise input with the
slice model and its two tests. Both preserve the field universe `u` and
the independent spectral-presentation universe `uQ`. The module built at
`d6b462be` with zero errors and warnings; inspection of the two
declarations gives only `propext`, `Classical.choice` and `Quot.sound`.
This is not an exact proof of A2.

```lean
import Langlands.Global.Factors.CuspidalPairPartialGammaGlobalTCReduction
import Langlands.Global.Factors.CuspidalPairPartialGammaTCReduction
import Langlands.Global.RankinSelberg.ArchimedeanCentralSignProof
import Langlands.Global.RankinSelberg.ArchimedeanFactorizationConditional
import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationLocalFEReduction
import Langlands.Global.RankinSelberg.EqualAnalyticProof
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationProof
import Langlands.Global.RankinSelberg.EqualEulerFactorizationProof
import Langlands.Global.RankinSelberg.EqualInfiniteWhittakerSliceReduction
import Langlands.Global.RankinSelberg.EqualSemilocalFactorizationReductionTC
import Langlands.Global.RankinSelberg.EqualUnfoldingProof
import Langlands.Global.RankinSelberg.UnequalAnalyticProof
import Langlands.Global.RankinSelberg.UnequalDualEulerFactorizationProof
import Langlands.Global.RankinSelberg.UnequalEulerFactorizationProof
import Langlands.Global.RankinSelberg.UnequalSemilocalArchimedeanReduction
import Langlands.Global.RankinSelberg.UnequalUnfoldingProof

/-! Development check for the totally complex completed equation (input A2 of the route of this note).
These conditional compositions still take unrestricted pointwise factorization or slice
inputs, not just inputs over totally complex number fields. -/

universe u uQ

set_option autoImplicit false

namespace Langlands.Correspondence.HenniartRouteA2

open Langlands.Global Langlands.Global.RankinSelbergGlobal

private theorem completedEquationTC_of_factorization
    (hFac : ArchimedeanFactorizationStatement.{u, uQ})
    (hU : ComplexLocalUnequalFunctionalEquationStatement)
    (hE : ComplexLocalEqualFunctionalEquationStatement) :
    CuspidalPairCompletedEquationTCStatement.{u, uQ} := by
  have hC := complexPlaceFunctionalEquationLocalFEReduction.{u} hU hE
  have hUS := unequalSemilocalComplexReduction.{u, uQ} ⟨hC, hFac, archimedeanCentralSign⟩
  have hES := equalSemilocalReductionTC.{u, uQ}
    (equalSemilocalFactorizationReductionTC.{u, uQ} hC.2 hFac.2 archimedeanCentralSign)
  exact cuspidalPairPartialGammaTCReduction.{u, uQ}
    (cuspidalPairPartialGammaGlobalTCReduction.{u, uQ}
      UnequalAnalytic.unequalAnalyticStatement_proof unequalUnfoldingStatement_proof
      unequalEulerFactorization unequalDualEulerFactorization hUS
      EqualAnalytic.equalAnalyticStatement_proof equalUnfoldingStatement_proof
      equalEulerFactorization equalDualEulerFactorization hES)

/-- The two pointwise factorizations and the two complex local equations suffice for A2. -/
theorem completedEquationTC_of_pointwise
    (hUF : UnequalPointwiseFactorizationStatement.{u, uQ})
    (hEF : EqualPointwiseFactorizationStatement.{u, uQ})
    (hU : ComplexLocalUnequalFunctionalEquationStatement)
    (hE : ComplexLocalEqualFunctionalEquationStatement) :
    CuspidalPairCompletedEquationTCStatement.{u, uQ} :=
  completedEquationTC_of_factorization (archimedeanFactorizationFromPointwise hUF hEF) hU hE

/-- Alternative: separate the equal-rank factorization into the slice model and local tests. -/
theorem completedEquationTC_of_equalSlice
    (hUF : UnequalPointwiseFactorizationStatement.{u, uQ})
    (hModels : InfiniteWhittakerSliceModelStatement.{u, uQ})
    (hReal : RealEqualPlaceTestsStatement.{u})
    (hComplex : ComplexEqualPlaceTestsStatement.{u})
    (hU : ComplexLocalUnequalFunctionalEquationStatement)
    (hE : ComplexLocalEqualFunctionalEquationStatement) :
    CuspidalPairCompletedEquationTCStatement.{u, uQ} :=
  completedEquationTC_of_pointwise hUF
    (equalPointwiseOfInfiniteTests (equalInfiniteWhittakerTest_of_local hModels hReal hComplex))
    hU hE

end Langlands.Correspondence.HenniartRouteA2
```

### D and the three links

D and the three links are the following reduction statements:

- link 1, `Global.CuspidalPairFunctionalEquationReductionTCStatement`;
- link 2, `RelativeWeilGroup.AssociatedGammaReductionTCStatement`;
- link 3,
  `RelativeWeilGroup.AssociatedCuspidalFactorReductionTCStatement`;
- D, `Henniart.CandidateExistenceTCReductionStatement`.

All four exact reduction proofs entered the Library at
`6e9e589baa721ce995563f73f648b6f4e45718a1`:

| Reduction | Theorem and declaration-site module |
| --- | --- |
| link 1 | `Global.cuspidalPairFunctionalEquationReductionTC`, `Global/Factors/CuspidalPairFunctionalEquationReductionTCProof` |
| link 2 | `ClassFieldTheory.Global.RelativeWeilGroup.associatedGammaReductionTC`, `Automorphic/AssociatedGammaTCReductionProof` |
| link 3 | `ClassFieldTheory.Global.RelativeWeilGroup.associatedCuspidalFactorReductionTC`, `Automorphic/AssociatedCuspidalFactorReductionTC` |
| D | `Henniart.candidateExistenceTCReduction`, `Correspondence/HenniartCandidateExistenceTCReductionProof` |

Link 2 takes the totally complex A3 at `.{u, u}` as a hypothesis; it does
not prove A3. The proof of D applies
`candidateExistenceTCReductionStatement_of_exactStabilizer` to the proved
`candidateExistenceExactStabilizerTCReduction`. The A2, B3, C1 and C3
inputs of the combined totally complex route are not proved by these
links. Before `CandidateExistenceExactStabilizerTCReductionStatement` was
proved, the proof of D was expected to follow the published proof of
`candidateExistenceReduction`, with a variant of the globalization step
that records that the number field is totally complex, and totally complex
copies of the five lemmas that pass on Théorème 2.4:
`exists_witnessedGenerator_realizeExact`,
`exists_witnessedGenerator_inducedReciprocity`,
`exists_weilImage_realizeExact_continuousInduce`,
`exists_weilImage_realizeExact_generator` and
`henniartGlobalization_of_inputs`. The published proof of
`CandidateExistenceExactStabilizerTCReductionStatement` takes this route
for the exact-stabilizer form, through the module
`Global/Arithmetic/HenniartGlobalizationExactStabilizerTC`.

D keeps Harris's Prop. 4.8 unchanged. Its fourteen-input reduction still
reaches the archimedean parameters at real places through the rigidity
input, `CuspidalSpectralRigidityStatement`, and the pole statement
`CuspidalPairPoleStatement`. Rigidity can also be proved by the route of
Jacquet–Shalika without archimedean parameters. That route is not stated
in the Library, and it still uses an archimedean nonvanishing result at
real places (Jacquet–Shalika I, (3.17)). On 15 November 2026 the operator
chose, between totally complex forms of the pole statement, of input 9 and
of inputs 11–14, and that route, the totally complex forms. The
Jacquet–Shalika route stays an alternative, with no statements in the
Library. Four statement modules state the totally complex forms, with the
same convention as A–D:

| Label | Module | Content |
| --- | --- | --- |
| H1 | `Global/Factors/CuspidalPairPoleTCStatement` | `Global.CuspidalPairPoleTCStatement`; its archimedean part involves only `GL_n(ℂ)` |
| H2 | `Automorphic/Unramified/CuspidalSpectralRigidityTCStatement` | input 9: `CuspidalSpectralRigidityTCStatement` and its three components |
| H3 | `Automorphic/Unramified/CyclicTransferInputsTCStatement` | inputs 11–14: `CyclicRegularInductionTCStatement`, `CyclicRegularOrbitLiftTCStatement`, `CyclicStableDescentTCStatement`, `CyclicWeakInductionSupercuspidalTCStatement` |
| H4 | `Global/Arithmetic/HarrisProposition48ReductionTCStatement` | `Global.Harris.Proposition48ReductionTCStatement`, which concludes the unchanged `Proposition48Statement`, and the totally complex forms of inputs 5, 6 and 10 |

The published inputs 5, 6 and 10 take inputs 9–14 as hypotheses, so H4
restates them with the totally complex hypotheses. The prime and singleton
forms imply the published ones, and inputs 9 and 10 together imply the
totally complex form of 10. The totally complex reduction does not imply
the published one. Every field to which the reduction applies inputs 9–14
is a CM field or a finite extension of one, hence totally complex
(`NumberField.IsCMField.isTotallyComplex`,
`NumberField.isTotallyComplex_of_algebra`). All four are in the Library at
commit `314cfd1a`. The rigidity proof uses Jacquet–Shalika I (5.2)–(5.3)
over the same field, and `CuspidalSelfPairContinuationStatement`
(Jacquet–Shalika I, Lemma 5.2) and
`CuspidalPairAbsoluteConvergenceReductionStatement` (Theorem 5.3) quantify
over all number fields. They have no totally complex forms. Instead, the
planned proof of the totally complex rigidity proves them for the one
field as helper lemmas: the Landau reduction of
`CuspidalPairAbsoluteConvergenceReductionStatement` works field by field,
and the route of `CuspidalSelfPairContinuationStatement` through the pole
statement applies it only over that field. That proof likewise uses only
the complex-place part of the archimedean pair regularity
(`CuspidalArchimedeanPairRegularityStatement`).

A proof of this kind existed on 17 November 2026 outside the Library. In
it, the totally complex rigidity follows from the totally complex pole
statement H1 together with three published statements in their
unrestricted form: the boundary nonvanishing of Shahidi
(`CuspidalPairBoundaryNonvanishingStatement`), the archimedean pair
regularity (`CuspidalArchimedeanPairRegularityStatement`) and the p-adic
pair L-polynomial nonvanishing
(`RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement`). It
states the pole statement over one field in a helper module and proves the
Jacquet–Shalika reductions over that field. It needs these inputs and the
totally complex pole statement to be proved.

Premise 2. The Library proves the counting reduction of Henniart 1988,
§2.8, in orbit form: `Henniart.numericalOrbitReduction` (module
`Correspondence/HenniartNumericalReductionProof`) proves
`Henniart.NumericalOrbitReductionStatement`. That statement says that
`NumericalSurjectivityStatement` follows from two hypotheses:
`NumericalOrbitCountStatement` (for every p-adic field, rank and
conductor, the unramified-twist orbit strata on the Weil and supercuspidal
sides are finite and have equal cardinality), and finiteness of the
conductor `Numerical.conductor K π` of every supercuspidal class `π`. A
search of the Lean sources at commit `544dba09` found no proof of either
hypothesis. The operator decided on 13 November 2026 that conductor
finiteness of supercuspidal classes is not part of the proof of numerical
surjectivity but comes from compact-open finiteness (Bernstein–Zelevinsky
1976, Cor. 4.15) and the conductor theorem.
`Henniart.supercuspidalCompactOpenFiniteness` (module
`Correspondence/SupercuspidalCompactOpenFinitenessProof`) proves
`Henniart.SupercuspidalCompactOpenFinitenessStatement`. That statement
says that only finitely many supercuspidal classes have a given central
character and a nonzero vector fixed by a given compact open subgroup. It
does not say that every supercuspidal class has a nonzero vector fixed by
one of the last-row congruence subgroups that define
`Numerical.conductor`, which is what conductor finiteness asserts. The
search above found no proof of conductor finiteness. Since 15 November
2026, the route of numerical surjectivity takes conductor finiteness from
the supercuspidal p-adic variant of premise 3 instead; see premise 3
below. A route-study note, [Henniart's numerical correspondence: route
study for the orbit counts](numerical-count-route-study.md), compares
Henniart's 1988 route to the orbit counts with a route through explicit
counts.

`NumericalOrbitCountStatement` has three conjuncts for each p-adic field
`K`, rank `k + 1` and conductor `a`: the Weil-side orbit stratum is
finite, the supercuspidal orbit stratum
`Numerical.supercuspidalOrbitStratum K k a` is finite, and the two have
the same `Set.ncard`. On 13 November 2026 the operator approved the first
lemma proposed in the route-study note (U1): the finiteness of the supercuspidal
orbit strata, as a statement and its proof. Both are in the Library:

- The statement
  `Henniart.SupercuspidalOrbitStratumFinitenessStatement.{uK, uV}` (module
  `Correspondence/HenniartOrbitStratumFinitenessStatement`). It says that
  for every p-adic field `K`, rank `k + 1` and conductor `a`, the set
  `Numerical.supercuspidalOrbitStratum.{uK, uV} K k a` is finite: the
  second conjunct above.
- Its proof: `Henniart.supercuspidalOrbitStratumFiniteness` (module
  `Correspondence/HenniartOrbitStratumFinitenessProof`) proves
  `SupercuspidalOrbitStratumFinitenessStatement.{uK, uV}` at independent
  universes. It is in the Library at commit `2016a0d9`.

The proof twists each orbit by an unramified character to a representative
whose central character is trivial at the scalar uniformizer and on the
central elements of the level-`a` subgroup. Only finitely many such
central characters exist, so each orbit meets one of finitely many sets
`SupercuspidalClass.centralLevelStratum χ a`. Each of these is finite by
the published `Henniart.CompactOpenFiniteness.centralLevelStratum_finite`
(Bernstein–Zelevinsky 1976, Cor. 4.15, for p-adic fields). This proves the
second conjunct of `NumericalOrbitCountStatement` only. The operator did
not approve the second lemma proposed in the note (U2), which would derive the
counts from a bijective numerical injection in every rank. The operator
judged it circular for this route: every known source of such an injection
is a local Langlands correspondence whose proof uses the numerical
theorem.

The program for the numerical step (operator decisions of 16 November
2026). The operator decided that the proof of numerical surjectivity
follows Option II of the operator's numerical note (literature source
`operator-numerical-llc-route-2026-11-16`, section "The recommended route:
Option II in detail"): Henniart's architecture, with the count on the GL
side done by simple types, without the Jacquet–Langlands correspondence
and without §7 of Henniart 1988. The glue, the statements of the four
inputs below and the conditional assembly are stated in the Library; they
are listed after the programs below. The note derives the two open
conjuncts of `NumericalOrbitCountStatement`, the Weil-side finiteness and
the equality of the counts, by an elementary argument (a base case at
small slopes and a descent along a tower of cyclic extensions of prime
degree) from four inputs. In the words of the operator's plan note (source
`operator-external-inputs-plan-2026-11-16`, Section 1.3, with the
interfaces of its Section 2):

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
statements below state (I3) and (I4), and (I2) in its p-adic form. The
operator's decision names the proof programs:

| Input | Scope of the proof program |
| --- | --- |
| (I1), D2 | Bushnell–Kutzko simple types for GL_n over a nonarchimedean local field, as far as the numerical step needs them, and the bound (I1) for every p-adic field |
| (I3), E2 | the simple trace formula of Deligne–Kazhdan type for GL_n over a number field with its twisted form for a cyclic extension, the local harmonic analysis on the regular elliptic set and the transfer of test functions; from them local cyclic base change of prime degree (I3), local automorphic induction at a non-split place (B4) and the statements B5, B6 and B7 |
| (I2), E1a | the Library's Galois-side layer extended from finite extensions of `Q_p` to nonarchimedean local fields of both characteristics, and the close-fields statement E1a |
| (I2), E1b | the numerical consequence of Laumon's local Fourier transform for a local field of characteristic `p`: equal numbers of unramified-twist orbits in the strata `W_X(d, s, f)` and `W_X(d + s, s, f)` |

None of these programs covers (I4). Its proof is global: by the plan note
(Section 2.5), it reads the candidate off the automorphic representations
of Harris's proposition and needs B1–B3 for them, C2, and the
compatibility of global base change with the local maps of E2 at the place
of interest (Arthur–Clozel, Ch. III, Thm 5.1). On 17 November 2026 the
operator decided that (I4) gets a proof program of its own within the
route of this note (Option (a)). Its target is the abstract (I4) of the
rank-bounded statement of Option II, and its first statement states E3 for the
Library's candidate together with the reduction "candidate form implies
the abstract (I4)". It takes B1–B3, C2 and E2 as published statements. It
takes Arthur–Clozel III.5.1 in the restricted form of the plan note's
Section 4.6, stated in the exact-stabilizer branch. Its proofs are to be
decomposed only once those statements are in the Library. See "Input (I4):
the proof program" below.

The statements of Option II. The modules below follow the operator's
amendment of 17 November 2026. Each gives definitions and Prop-valued
statements in a module under `Langlands/Correspondence/` with the names it
fixes. None of them proves anything. At commit `8aede86c` the Library has
the modules of the polar-part model and of the refined strata and of no
other module in the table.

The modules depend on one another: (LD), (I1), the twist Swan bound, the
truncated Weil-side layer, (I3), the base case and the conditional
assembly use the refined strata; the rank-bounded (I4) and the tower lemma
use (I3), which itself uses the refined strata and the twist Swan bound;
the truncated Weil-side layer also uses (LD), the base case (LD) and (I1),
and the conditional assembly (LD), (I1), the twist Swan bound, (I3) and
the rank-bounded (I4). The program for (I4) below starts from the
rank-bounded (I4). The modules entered the Library in this order: the
refined strata at commit `d26f6985`; (I1)
(`HenniartGLUpperBoundStatement`) and the twist Swan bound
(`HenniartTwistSwanStatement`) at commit `f050c0b1`, neither statement
proved; (LD) (`HenniartLaumonDeligneStatement`) at commit `c0148597`, not
proved; (I3) (`HenniartCyclicBaseChange`) at commit `24390f9f`, its
statement `LocalCyclicBaseChangeStatement` not proved. Three further
statements were not in the Library at commit `24390f9f`:

- module `Correspondence/HenniartWeilElementaryLayer`: six statements on
  the Weil side (`WeilUnramifiedDescentCountStatement`,
  `WeilRankOneCountStatement`, `WeilTameReductionStatement`,
  `WeilConductorCountStepStatement`,
  `WeilTruncatedConductorCountStatement` and
  `LaumonDeligneWeilCountStatement`) with the predicates
  `IsUnramifiedOfDegree` and `IsTameTotallyRamifiedOfDegree`;
- module `Correspondence/HenniartCompatibleInjections`:
  `Henniart.CompatibleNumericalInjectionsStatement`, the statement (I4)
  described below;
- module `Correspondence/HenniartNumericalBaseCaseStatement`:
  `Henniart.NumericalBaseCaseStatement`, which derives `C(K, x, N)` for
  slopes `x < e_K` from (I1), (LD) and numerical injections in ranks up to
  `N`.

The truncated Weil-side layer and the base case were published at
`95d37e11`. The six statements of the layer are not a proof of the Weil
count; `WeilTruncatedConductorCountStatement` and
`NumericalBaseCaseStatement` are separate targets of proof. The
rank-bounded (I4) was published at `6e9e589b`; the conditional assembly
and the program for (I4) use it. The tower lemma does not use (I4): it
uses only the cyclic-step definitions (`CyclicPrimeStep` and
`herbrandPsi`) of the (I3) module, published at `24390f9f`. The tower
statement was also published at `6e9e589b`. It is not a proof of the tower
lemma.

| Label | Module | Content |
| --- | --- | --- |
| polar-part model | `HenniartPolarPart` (in the Library) | the polar-part model `ν(n, f, s; q)` and `PolarPartClosedFormulaStatement`, `PolarPartCountingIdentityStatement`, `PolarPartTruncatedUniquenessStatement`; at commit `24390f9f` the first two are proved (see below) |
| refined strata | `HenniartRefinedStrata` (in the Library) | Swan exponents `Numerical.HasWeilSwan` and `Numerical.HasSupercuspidalSwan`, torsion numbers `Numerical.weilTorsionNumber` and `Numerical.supercuspidalTorsionNumber`, the refined orbit strata `W_K(n, s, f)` and `S_K(n, s, f)` (`Numerical.weilRefinedStratum` and `Numerical.supercuspidalRefinedStratum`), the counts `Numerical.weilTwistIrreducibleCount` and `Numerical.weilConductorCount`, the statement `C(L, x, N)` (`Numerical.CountsAgreeUpToSlope`), `WeilArtinConductorExistenceStatement` (Artin integrality) and `RefinedStrataStatement`, the conjunction of `NumericalInjectionRefinedStrataStatement` and `CountingSurjectivityStatement` (the counting-versus-surjectivity lemma) |
| (LD) | `HenniartLaumonDeligneStatement` (in the Library at commit `c0148597`) | (I2): `LaumonDeligneCountStatement`, the statement (LD) |
| (I1) | `HenniartGLUpperBoundStatement` (in the Library at commit `f050c0b1`) | (I1): `SupercuspidalStratumUpperBoundStatement` |
| twist Swan bound | `HenniartTwistSwanStatement` (in the Library at commit `f050c0b1`) | twists by characters of `K^×` and `SupercuspidalTwistSwanBoundStatement`, `sw(χπ) ≤ max(sw π, n·sw χ)` |
| truncated Weil-side layer | `HenniartWeilElementaryLayer` (published at `95d37e11`) | the truncated Weil-side counts: unramified descent, rank one, tame reduction, Henniart's Corollaire 1.4, the truncated Théorème 1.3 and the close-range count from (LD) |
| (I3) | `HenniartCyclicBaseChange` (in the Library at commit `24390f9f`) | cyclic steps of prime degree `Numerical.CyclicPrimeStep`, the Herbrand function, the weak base-change predicate `Numerical.IsWeakCyclicBaseChange` and (I3): `LocalCyclicBaseChangeStatement` |
| rank-bounded (I4) | `HenniartCompatibleInjections` (published at `6e9e589b`) | (I4): `CompatibleNumericalInjectionsStatement` |
| base case | `HenniartNumericalBaseCaseStatement` (published at `95d37e11`) | the base case `NumericalBaseCaseStatement` at slopes below `e_L` |
| tower lemma | `HenniartCyclicTower` (published at `6e9e589b`) | the tower lemma `CyclicTowerStatement` |
| conditional assembly | planned `HenniartNumericalDescentStatement` (not in the Library at `d6b462be`) | `BaseChangeSlopeStatement`, `DescentStepStatement` and the conditional assembly `NumericalDescentStatement` |

The rank-bounded statement `CompatibleNumericalInjectionsStatement` states
(I4) in an abstract form (see "Input (I4): the proof program" below). Let
`p` be a prime, `S` a cyclic step of prime degree with base `L` and top
`M`, and `N` a rank bound such that `Numerical.SurjectiveBelowRank N`
holds. That hypothesis says that every numerical injection in a rank below
`N`, over any p-adic field, is surjective. Then there are rank-bounded
families `φL` and `φM`, of type `∀ k, k + 1 ≤ N → IrreducibleWeilClass _
k.succPNat → SupercuspidalAutomorphicClass _ k.succPNat`, over `L` and
over `M`. Each of them is a numerical injection in every rank up to `N`.
There is also a map `Ch` that is a weak cyclic base change for `S`, and
the three satisfy two conditions:

- (CI1) of the operator's numerical note,
  `Numerical.IsBaseChangeCompatible S Ch N φL φM`: `Ch` sends `φL(σ)` to the
  image under `φM` of the decomposition of the restriction of `σ` to `W_M`;
- `Numerical.ReflectsGaloisInvariance S N φM`: if `φM(τ)` is fixed by
  `Gal(M/L)`, then `τ` is fixed by the conjugation action
  `Numerical.weilConjugate` of `W_L`.

The second condition replaces (CI2); it is what Remark `rem:CI2` of the
numerical note says (CI2) is used for. The families are bounded in their
type because a family defined in every rank would need supercuspidal
classes in every rank where irreducible Weil classes exist, which the
Library does not prove. The statement implies (I3) for the same `Ch`, and
it does not name the Library's candidate. `DescentStepStatement` of the
conditional assembly uses the same rank-bounded families. The planned
proof of `NumericalDescentStatement` is by induction on `N` over all
fields, and the induction supplies `SurjectiveBelowRank N`.

The conditional assembly `NumericalDescentStatement.{uK, uW, uV}` takes
five premises and concludes `C(K, x, N)` for every p-adic field `K`, slope
`x` and rank bound `N`, together with `NumericalSurjectivityStatement.{uK,
uW, uV}` and `NumericalOrbitCountStatement.{uK, uW, uV}`. The conductor
theorem enters through the proved
`Conductor.supercuspidalPadicConductorExponent`, so it is not a premise.
The five premises and the programs for their proofs, as of 17 November
2026:

| Premise | Statement | Proof |
| --- | --- | --- |
| (I1) | `SupercuspidalStratumUpperBoundStatement` | the simple-types program (input I1); a reduction of (I1) to the statements A1–A3 on supercuspidal classes and maximal simple types and Q3 on simple types over a simple character is planned |
| (LD), input (I2) | `LaumonDeligneCountStatement` (module `Correspondence/HenniartLaumonDeligneStatement`, in the Library at commit `c0148597`, unproved) | the programs for E1a and E1b; the statements of the two halves need the Weil groups in characteristic `p` of the E1a program |
| (I4) | `CompatibleNumericalInjectionsStatement` | the program for (I4) below |
| twist Swan bound | `SupercuspidalTwistSwanBoundStatement` | the simple-types program (the normalized level and the Swan conductor of supercuspidals) |
| Artin integrality | `WeilArtinConductorExistenceStatement` | a separate proof (proved, see below) |

Each statement of the glue is a separate target of proof, among them the
conditional assembly, the base case, the one-step descent, the tower lemma
and slopes under base change. The first to be proved: at commit `c0148597`
the Library proves `RefinedStrataStatement.{uK, uW, uV}`, the conjunction
of the preservation of refined strata by numerical injections and the
counting-versus-surjectivity lemma, without added hypotheses, as
`Langlands.Henniart.refinedStrata` (module
`Correspondence/HenniartRefinedStrataProof`). At commit `86dbe494` no
other statement of the glue (the polar-part statements,
`WeilArtinConductorExistenceStatement` and the statements of (LD), (I1),
the twist Swan bound, the truncated Weil-side layer, (I3), the
rank-bounded (I4), the base case, the tower lemma and the conditional
assembly) was proved. At commit `24390f9f` two polar-part statements are
also proved: `Henniart.polarPartClosedFormula :
PolarPartClosedFormulaStatement` (module
`Correspondence/HenniartPolarPartClosedFormulaProof`) and
`Henniart.polarPartCountingIdentity : PolarPartCountingIdentityStatement`
(module `Correspondence/HenniartPolarPartCountingIdentityProof`). At
`d6b462be` the third is also proved,
`Henniart.polarPartTruncatedUniqueness` (module
`Correspondence/HenniartPolarPartTruncatedUniquenessProof`). Moreover,
`Henniart.weilArtinConductorExistence` (module
`Correspondence/HenniartWeilArtinConductorExistenceProof`) proves the
Artin integrality premise at independent `uK` and `uW`. This discharges
one of the five inputs of the assembly, not the assembly itself. The tower
lemma is now stated in the Library. For that proof,
`Correspondence/HenniartCyclicStepHerbrandStatement` states
`Henniart.CyclicPrimeStepHerbrandPsiStatement`, comparing the explicit
step function with the relative inverse Herbrand function of an isomorphic
extension inside the algebraic closure of the base. This is a statement,
not a proof of the comparison or of the tower lemma.

Three of the operator's programs comprise the following units of
definitions and statements.

- For the simple-types program (input I1): lattice chains and hereditary
  orders, cuspidal representations of `GL_n` over a finite field, the
  label sets of Bushnell–Kutzko, strata and minimal elements, simple
  characters, Heisenberg representations, β-extensions and simple types,
  and the normalized level with the formula that the Swan conductor of a
  supercuspidal is `n` times its level (the start of the part of the
  program that the twist Swan bound needs).
- For the trace-formula and base-change program (input I3): twisted
  conjugation, the norm map of Henniart–Lemaire, orbital and σ-orbital
  integrals on `GL_n`, the trace of a trace-class integral operator, the
  abstract simple twisted trace formula, and Satake characters, the
  unramified base-change homomorphism and the base-change fundamental
  lemma.
- For the Galois-side program (input I2, E1a): modules that generalize to
  nonarchimedean local fields of both characteristics the Library's
  ramification filtrations, its local Weil group, the relative Herbrand
  function, Artin and Swan conductors, and irreducible Weil classes,
  twists and the refined strata. Further modules state Herbrand's theorem
  and the properties of the upper filtration, the independence of Artin
  and Swan conductors from the presentation and the single upper break of
  an irreducible Weil representation, and the correspondence between
  unramified-twist orbits of Weil classes and finite-image Galois
  representations.

Further units of definitions and statements of the same programs follow.
None of them is a proof.

- For the simple-types program:
  - supercuspidal representations that contain maximal simple types;
  - exhaustion, the statement that every supercuspidal representation
    contains a simple type;
  - conjugacy classes of simple strata and of simple characters with their
    Bushnell–Kutzko labels;
  - simple types over a simple character, with the label bound for maximal
    simple types;
  - supercuspidal classes and maximal simple types: every class contains
    one, the type fixes the torsion number and the Swan exponent, and
    conjugate types give unramified twists.
- For the trace-formula and base-change program:
  - the finiteness of rational conjugacy classes meeting a compact set
    that is regular elliptic at one place;
  - twisted characters, σ-lifts and Shintani lifts;
  - the twist `θ` of the simple twisted trace formula;
  - tempered representations, σ-discrete series and twisted
    pseudo-coefficients;
  - functions whose (twisted) orbital integrals vanish off the elliptic
    set;
  - local cyclic base change for discrete series;
  - cusp forms, the existence of supercuspidal representations and
    supercuspidal pseudo-coefficients;
  - split places and the transfer of elliptic-supported functions;
  - the σ-lift of a supercuspidal representation as a product of Galois
    conjugates;
  - the conductor identity for that σ-lift (the conductor formula of E2);
  - the compatibility of σ-lifts with parabolic induction;
  - split twisted orbital integrals of decomposed functions.
- For the Galois-side program:
  - the close-fields statement E1a in group form,
    `CloseFieldsGaloisQuotientStatement`;
  - the Kummer-step and Kummer-tower ramification lemmas;
  - the field-of-norms premise for the Kummer tower and its implication to
    E1a;
  - the truncation lemma for p-adic fields.

At commit `ab9053b1` the Library has the module of the Kummer-step and
Kummer-tower lemmas,
`LocalFactor/Ramification/Herbrand/KummerTowerStatement` (namespace
`Langlands.Ramification.Kummer`). It defines the Kummer tower of a
uniformizer and states six propositions: `KummerStepUpperSupStatement`,
`KummerStepHerbrandPsiStatement`, `HerbrandPsiTruncationStatement`,
`KummerTowerUpperSupStatement`, `KummerTowerHerbrandPsiStatement` and
`KummerTowerLimitUpperSupStatement`. It proves none of them. At commit
`d26f6985` the third is proved: `herbrandPsiTruncation :
HerbrandPsiTruncationStatement.{u}` (module
`LocalFactor/Ramification/Herbrand/KummerTruncationProof`). At commit
`ba9d1e9a` the first is proved: `kummerStepUpperSup :
KummerStepUpperSupStatement.{u}` (module
`LocalFactor/Ramification/Herbrand/KummerStepUpperSupProof`). At commit
`c0148597` the second is proved: `kummerStepHerbrandPsi :
KummerStepHerbrandPsiStatement.{u}` (module
`LocalFactor/Ramification/Herbrand/KummerStepHerbrandPsiProof`). The other
three, the tower statements, were unproved at commit `86dbe494`. At commit
`24390f9f` the fourth is proved: `kummerTowerUpperSup :
KummerTowerUpperSupStatement.{u}` (module
`LocalFactor/Ramification/Herbrand/KummerTowerUpperSupProof`).
`KummerTowerHerbrandPsiStatement` and `KummerTowerLimitUpperSupStatement`
are unproved at that commit. At commit `d26f6985` the Library has the
module of the truncation lemma,
`LocalFactor/Ramification/Herbrand/TruncationQuotientStatement`. It
defines the truncated quotients and states, among others,
`KummerStageGaloisQuotientStatement` and
`KummerStageWeilQuotientStatement`: every finite stage `K_n =
F(π^(1/p^n))` of the Kummer tower has the same filtered Galois,
respectively Weil, quotients as `F` for upper numbering `-1 ≤ x ≤ p
e/(p-1)`. These two are statement definitions, not proofs. At commit
`24390f9f` four auxiliary statements of the same module are proved
(`truncationGaloisComap`, `truncationWeilComap`, `truncationWeilQuotient`
and `truncationWeilDegree`, in modules
`LocalFactor/Ramification/Herbrand/Truncation…Proof`), while
`TruncationGaloisQuotientStatement`, `TruncationWeilRestrictionStatement`
and the two Kummer-stage statements were unproved at that commit. At
`d6b462be`, five further exact proofs are available under
`LocalFactor/Ramification/Herbrand/`:

| Theorem | Declaration-site module (relative to that directory) |
| --- | --- |
| `kummerTowerHerbrandPsi` | `KummerTowerHerbrandPsiProof` |
| `kummerTowerLimitUpperSup` | `KummerTowerLimitUpperSupProof` |
| `truncationGaloisQuotient` | `TruncationGaloisQuotientProof` |
| `truncationWeilRestriction` | `TruncationWeilRestrictionProof` |
| `kummerStageWeilQuotient` | `KummerStageWeilQuotientProof` |

The Kummer-stage Galois quotient target is still open despite the auxiliary
Galois quotient theorem. These results do not prove the close-fields count
or (LD).

Further units of the programs follow; those of the exact-stabilizer branch
are listed under premise 1.

- For the simple-types program:
  - the reduction of the twist Swan bound to the level statements L0, L2
    and T2. At commit `24390f9f` its statement is in the Library:
    `Henniart.SupercuspidalTwistSwanBoundReductionStatement.{uK, uV}`
    (module `Correspondence/HenniartTwistSwanReductionStatement`) states,
    without proof, that L0, L2 and T2 imply
    `SupercuspidalTwistSwanBoundStatement.{uK, uV}`. At `d6b462be` all
    three inputs are proved (see below), but the reduction itself still
    needs a proof;
  - targets of proof for Bushnell–Kutzko 1993, §§1.1–1.2: the radical
    filtration of a hereditary order, the normalizer of a hereditary
    order, the additive duality of the filtrations with the characters
    `ψ_b`, and lattice chains normalized by a subfield with the relative
    hereditary order.
- For the trace-formula and base-change program:
  - the predicate that a local base-change map on supercuspidal classes is
    certified by σ-lifts, `IsSigmaLiftOnSupercuspidals` (Henniart–Lemaire
    II.2.7), which E2 is to use;
  - a proof of the formula for the trace of a trace-class integral
    operator as the integral of its kernel on the diagonal, after
    Brislawn, for the proof of the abstract simple twisted trace formula;
  - a proof of the finiteness of rational conjugacy classes meeting a
    compact set that is regular elliptic at one place;
  - statements on the factorization of twisted orbital integrals of
    product functions over products of groups.
- For the Galois-side program: a proof of each of the six statements of
  the Kummer-step and Kummer-tower module described above.
- For Laumon's numerical statement (E1b): definitions of the continuous
  irreducible l-adic representation classes of the absolute Galois group
  of a nonarchimedean local field, with their unramified twists. Laumon's
  local Fourier transform acts on these classes, so they come before any
  statement about the transform.

Further modules, among them the following; the list is not complete, and the
descriptions follow the titles of the modules. The proofs for the
archimedean premises are listed in the [A2
chain](#a2-the-totally-complex-completed-rankinselberg-equation), and
those of the exact-stabilizer branch under premise 1.

- For the simple-types program: proofs of
  `BushnellKutzkoLabelCountStatement` (module
  `Correspondence/BushnellKutzkoLabelCount`) and for the level statements:
  L0, `NormalizedLevelExistenceStatement`, L1,
  `FundamentalStratumLevelStatement`, L2, `NormalizedLevelTwistStatement`,
  and T2, `SupercuspidalSwanLevelStatement`. The four level statements are
  in modules of the same names under `BushnellKutzko/`. At commit
  `f050c0b1` the label count is proved:
  `Henniart.bushnellKutzkoLabelCount` (module
  `Correspondence/BushnellKutzkoLabelCountProof`). The four level
  statements are unproved at that commit. At commit `24390f9f` L0 and L1
  are proved: `BushnellKutzko.normalizedLevelExistence :
  NormalizedLevelExistenceStatement.{uK, uV}` (module
  `BushnellKutzko/NormalizedLevelExistenceProof`) and
  `BushnellKutzko.fundamentalStratumLevel :
  FundamentalStratumLevelStatement.{uK, uV}` (module
  `BushnellKutzko/FundamentalStratumLevelProof`). At `d6b462be`, L2 is
  proved by `BushnellKutzko.normalizedLevelTwist` (module
  `BushnellKutzko/NormalizedLevelTwistProof`) and T2 by
  `BushnellKutzko.supercuspidalSwanLevel` (module
  `BushnellKutzko/SupercuspidalSwanLevelProof`), at independent `uK`,
  `uV`.
- For the trace-formula and base-change program:
  - proofs of the norm lemma of cyclic base change,
    `CyclicNormLemmaStatement`, the Satake parametrization of spherical
    characters, `SatakeCharacterStatement`, and the transfer of regularly
    supported test functions, `RegularTransferStatement`. The three
    statements are in modules `BaseChange/Norm`,
    `BaseChange/SatakeCharacterStatement` and
    `BaseChange/RegularTransferStatement`; the first two were already in
    the Library at commit `70eba6bb`;
  - statements of the simple twisted trace formula for `Res_{L/K} GL_n`
    with cyclic `L/K`, the finite volume of twisted-centralizer quotients
    and the integrability of twisted orbit functions, the global base
    change trace identity, the global matching of orbital integrals, the
    realization of a cyclic extension of a p-adic field as the completion
    of a cyclic extension of number fields, and supercuspidal
    representations prescribed at finitely many places occurring, up to
    unramified twists, in one cuspidal automorphic representation;
  - proofs of the existence of the centralizer and quotient measures in
    the concordance of orbital integrals,
    `OrbitalMeasureExistenceStatement` (stated with the orbital
    integrals), and of norms near `1`, `NormNeighbourhoodStatement`
    (stated with the split places and the transfer of elliptic-supported
    functions). The two statements are in the modules
    `BaseChange/OrbitalMeasureExistenceStatement` and
    `BaseChange/NormNeighbourhoodStatement`;
  - two statements of premises of the twisted spectral expansion: Schur's
    lemma for isometric group actions on complex Hilbert spaces, with the
    equivalence of an irreducible closed invariant subspace of a Hilbert
    sum to one of its summands (step G-e), and the stability of the
    cuspidal `L²` subspace under the twisting operator of an automorphism
    of a reductive group scheme over a number field (step G-f).
- For the Galois-side program: proofs of
  `KummerStageGaloisQuotientStatement` and
  `KummerStageWeilQuotientStatement`, the two statements of the
  truncation-lemma module
  `LocalFactor/Ramification/Herbrand/TruncationQuotientStatement`
  described above.

Further modules on the route; the list is not complete:

- For numerical surjectivity, the two halves of input (I2) as separate
  statements: the count form of E1a for close fields, `T_K(d, s) = T_X(d,
  s)` for a p-adic field `K`, `X = F_q((t))` over its residue field and `s
  < d·e_K`, and Laumon's numerical statement E1b, `|W_X(d, s, f)| = |W_X(d
  + s, s, f)|` for `s ≥ 1` and `f` dividing `gcd(d, s)`. Both use the
  generalization of the Library's irreducible Weil classes, twists and
  refined strata to nonarchimedean local fields of any characteristic, and
  the first also uses the refined strata.
- For the Galois-side program: the implications from E1a in group form and
  from the field-of-norms premise for the Kummer tower to the count form
  of E1a.
- For finite abelian class field theory: the proof of the norm-kernel
  Hecke character (described under premise 2 above).

Further modules on the route; the list is not complete. Those of the
exact-stabilizer branch are described under premise 1, the complex Tate
statement in the [A2
chain](#a2-the-totally-complex-completed-rankinselberg-equation), and the
planned reduction of (I1) in the table of the five premises of the
assembly under premise 2.

- For the simple-types program: proofs of six statements of
  Bushnell–Kutzko (1993) on strata and minimal elements:
  `TameCorestrictionStatement`, `AdjointExactnessStatement`,
  `MinimalCriticalExponentStatement`, `SimpleIntertwiningStatement`,
  `StratumEquivalenceStatement` and `RefinementStatement`, all in the
  namespace `BushnellKutzko`. At commit `f050c0b1` the first two are
  proved (`BushnellKutzko.tameCorestriction` and
  `BushnellKutzko.adjointExactness`, modules
  `BushnellKutzko/TameCorestrictionProof` and
  `BushnellKutzko/AdjointExactnessProof`). At commit `24390f9f`
  `SimpleIntertwiningStatement` is also proved:
  `BushnellKutzko.simpleIntertwining : SimpleIntertwiningStatement`
  (module `BushnellKutzko/SimpleIntertwiningProof`). At `7ae0d83b` the
  other three are also proved: `BushnellKutzko.minimalCriticalExponent`
  (`BushnellKutzko/MinimalCriticalExponentProof`),
  `BushnellKutzko.stratumEquivalence`
  (`BushnellKutzko/StratumEquivalenceProof`) and
  `BushnellKutzko.refinement` (`BushnellKutzko/RefinementProof`). Each
  proves its exact Library statement. That does not prove
  `StratumApproximationStatement`.
- For Laumon's numerical statement (E1b): definitions of the Swan exponent
  and the refined twist-orbit strata of l-adic Galois classes and
  statements of four results of Henniart (1988), §§4.1–4.3, among them
  Laumon's twist-equivariant bijection, planned in a module
  `Correspondence/HenniartLadicStatement`, from which E1b is to be proved.
  They use the l-adic classes, whose module
  `Correspondence/HenniartLadicClasses` is in the Library at commit
  `f050c0b1`.
- For the trace-formula and base-change program, proofs of its statements.
  At commit `ba9d1e9a` the Library has, among others, the modules
  `BaseChange/FundamentalLemmaStatement`,
  `BaseChange/UnitFundamentalLemmaStatement`,
  `BaseChange/TwistedCharacter`,
  `BaseChange/SigmaLiftCharacterIdentityStatement`,
  `BaseChange/TwistedCharacterRegularValuesStatement`,
  `BaseChange/SplitMatchingStatement`,
  `BaseChange/OrbitalIntegralPositivityStatement`,
  `TraceFormula/GeneralLinearSimpleTraceFormulaStatement`,
  `TraceFormula/GeneralLinearCuspFormLocalVanishingStatement` and
  `Automorphic/GeneralLinearCuspidalSummandRealizationStatement`. At
  commit `f050c0b1` it also has, among others,
  `TraceFormula/GeneralLinearSimpleTwistedTraceFormulaStatement`,
  `TraceFormula/GeneralLinearBaseChangeTraceComparisonStatement`,
  `TraceFormula/GeneralLinearSupercuspidalGlobalizationStatement` and
  `TraceFormula/CyclicFieldGlobalizationStatement`. None of these
  statements is proved at commit `24390f9f` (`BaseChange/TwistedCharacter`
  only defines twisted characters and lifts). The two statements of the
  module `Automorphic/GeneralLinearCuspidalSummandRealizationStatement`,
  on the realization of cuspidal summands, are targets of proof of the
  global program. Further targets of proof of the base-change program are
  separation of bounded characters, Schur's lemma for Hilbert sums, traces
  along Hilbert sums, the twist invariance of the cuspidal subspace and
  the globalization of a cyclic extension of local fields; the trace
  comparisons between the positive and the norm-one quotients;
  `SplitMatchingStatement` and `OrbitalIntegralPositivityStatement`;
  twisted centralizers and the adelic points of `Res_{L/K} GL_n`;
  `GeneralLinearCuspFormLocalVanishingStatement` and the local trace
  factorization on a cuspidal summand; and
  `UnitFundamentalLemmaStatement`. At commit `c0148597` the Library also
  has the statement modules
  `BaseChange/CuspidalSigmaLiftConductorStatement` (the conductor identity
  for the σ-lift of a supercuspidal representation, which is the conductor
  formula of E2), `BaseChange/SigmaLiftInductionStatement` (σ-lifts
  commute with irreducible normalized parabolic induction) and
  `TraceFormula/GeneralLinearEllipticCentralizerStatement` (for a rational
  element of `GL_n` that is regular elliptic at a finite place, the
  centralizer quotient has finite volume and the orbit function of a
  compactly supported continuous function is integrable). None of these
  three statements is proved at commit `24390f9f`. Further targets of
  proof are `FundamentalLemmaStatement`,
  `TwistedCharacterRegularValuesStatement`,
  `SigmaLiftCharacterIdentityStatement`, the ordinary and twisted spectral
  expansions `GroupSchemeTwistedCuspidalSpectralExpansionStatement` and
  `SigmaLiftInductionStatement`. A further statement says that at a finite
  place, the local factor of the trace on an irreducible cuspidal `L²`
  summand of `GL_{r+1}` over a number field is the character of the local
  component at that place (of a spectral presentation) of a cuspidal
  operator realization whose `L²` classes are dense in the summand. At
  commit `24390f9f` the Library also has the module of that statement
  (`TraceFormula/GeneralLinearCuspidalLocalComponentTraceStatement`), the
  abstract simple twisted trace formula
  (`TraceFormula/AbstractSimpleTwistedStatement`), and the statement
  modules `BaseChange/PseudoCoefficient`,
  `BaseChange/PseudoCoefficientExistenceStatement`,
  `BaseChange/TwistedPseudoCoefficientExistenceStatement`,
  `BaseChange/EllipticTransferStatement`,
  `BaseChange/SplitSigmaLiftStatement`,
  `BaseChange/CuspidalSigmaLiftExistenceStatement`,
  `BaseChange/CuspidalSigmaLiftStructureStatement`,
  `ClassField/Global/CyclicHasseNormStatement` and
  `Automorphic/CuspidalArithmeticSpectralTransportStatement`. None of the
  statements of these modules is proved at that commit.

At `d6b462be` the base-change line has these exact proofs (theorems in
namespace `Langlands.BaseChange`, modules listed under `Langlands/`):

| Theorem | Declaration-site module |
| --- | --- |
| `cyclicNormLemma` | `BaseChange/CyclicNormLemma` |
| `satakeCharacter` | `BaseChange/SatakeCharacter` |
| `orbitalMeasureExistence` | `BaseChange/OrbitalMeasureExistence` |
| `normNeighbourhood` | `BaseChange/NormNeighbourhood` |
| `orbitalIntegralPositivity` | `BaseChange/OrbitalIntegralPositivity` |
| `splitMatching` | `BaseChange/SplitMatching` |

These supply specific norm, character and orbital-integral results. In
particular, split matching is not general local transfer. None supplies
the local cyclic base-change statement (I3, E2).

Further modules on the route followed, among them those named in the last
item above and the statements for the two branches of the exact-stabilizer
form, which are described under premise 1. This list is not complete
either.

Further modules bearing on the route (the descriptions follow the titles of
the modules; the list is not complete):

- for the base-change program for input (I3): a proof of
  `CuspidalSigmaLiftConductorStatement`, and statements on cuspidal base
  change to a prime cyclic extension of a cuspidal representation with
  unitary central character that is supercuspidal at two split finite
  places, on local integrability of ordinary and twisted characters, on
  five local inputs of cyclic base change by the simple trace formula, and
  on cuspidal `L²` summands of `Res_{L/K} GL_{r+1}` and their local
  twisted traces;
- for the inputs of Harris's Prop. 4.8 and Thm 1.2 (premise 1): a proof of
  prime cyclic unitary isobaric base change over totally complex fields;
  modules on Clozel's division algebra, Kottwitz's multiplicity theorem and
  Clozel's transfer for Harris's cuspidal existence, on normalized Harris
  CM classes in the division case, and on discrete trace comparisons for
  prime cyclic descent and base change (Arthur–Clozel III.4.2(d)–(e));
  proofs of the totally complex cuspidal infinitesimal-character bridge,
  of Arthur–Clozel III.3.1 and of the assembly of the cuspidal case of
  Harris's Thm 1.2; algebraic Hecke character avatars; and proofs of the
  assembly of the cyclic stable descent theorem B1, of the cyclic regular
  induction input B2 and of the cyclic regular orbit-lift input B3;
- off the totally complex path: proofs of the real-place local functional
  equations.

So, once the glue is proved, premise 2 follows from the five premises of
the assembly, each of which has a program of proof.

Input (I4): the proof program. The program for (I4), decided by the
operator on 17 November 2026, starts from the rank-bounded (I4),
`CompatibleNumericalInjectionsStatement`. It consists of statements, each
with a separate proof. Its three statements are as follows.

1. E3 for the Library's candidate. The statement is
   `Henniart.CandidateBaseChangeCompatibilityStatement`, in the new module
   `Correspondence/HenniartCandidateBaseChangeCompatibility`. For every prime
   `p` and every step `S` there is one `Ch` that is a weak cyclic base change
   for `S`, with two properties. The first is (CI1), rank by rank, in every
   rank where the candidate `Extension.rankExtension` is defined (that is,
   where `StableExistsAt` holds). The second is the full (CI2) in those
   ranks, through `Numerical.weilConjugate` and `S.galoisConjugate`. The
   statement is rank by rank because in Henniart's induction stable
   existence in rank `n` comes from the ranks below `n`.
2. The reduction
   `Henniart.CandidateCompatibleNumericalInjectionsReductionStatement`:
   `CandidateExistenceStatement` and statement 1 imply
   `CompatibleNumericalInjectionsStatement`. It does not assume stable
   existence in all ranks, which would be circular. Instead it obtains stable
   existence and the numerical-injection property up to rank `N` from
   `SurjectiveBelowRank N`. For this it uses the Library's
   `rankOneStage_of_reciprocity`, `choiceIndependenceStep_of_inputs`,
   `stableSurjectiveAt_of_surjective` and the argument of
   `SupercuspidalConductor.surjectivityStepReduction`.
3. The final theorem, in the form of the end of Section 7.1 of the
   operator's numerical note. Candidate existence, statement 1 and the four
   other premises of `NumericalDescentStatement` imply
   `SupercuspidalCorrespondenceStatement`. Its proof is to compose statement 2,
   the planned proof `numericalDescent` of `NumericalDescentStatement`,
   the published
   `supercuspidalCorrespondenceHenniartSupercuspidalConductor` and
   `Conductor.supercuspidalPadicConductorExponent`. The target of premise
   2 stays the unconditional `NumericalSurjectivityStatement`; this
   theorem does not replace it.

The proof of statement 1 is global. It uses B1–B3, C2, E2 (the (I3) module) and
the restricted Arthur–Clozel III.5.1, all of which are to be statements of
the Library before it is decomposed. At commit `8aede86c` the Library has
the vocabulary of local components and supercuspidal support of isobaric
data and the norm-kernel character statement (described below), but not
(I3), the rank-bounded (I4) or the restricted III.5.1. (I3) entered the
Library at commit `24390f9f` (module
`Correspondence/HenniartCyclicBaseChange`), and the rank-bounded (I4) at
`6e9e589b`. This makes the statements of the program possible; it is not a
proof of (I4).

The restricted III.5.1 belongs to the exact-stabilizer branch. Its
statement is `RestrictedCyclicBaseChangeCompatibilityStatement`, in the
module
`Automorphic/Unramified/RestrictedCyclicBaseChangeCompatibilityStatement`.
For every prime `p` and every step `S` there is one `Ch` with
`IsWeakCyclicBaseChange S Ch`, chosen before all ranks and global data,
that satisfies the following compatibility.

- The global setting: `F` is a CM field, `E/F` is cyclic of degree
  `S.degree`, and `v` and its complex conjugate `c(v)` are distinct places of
  `F`, each with a unique place of `E` above it. The local fields of `S` are
  identified with `F_v` and `E_w` compatibly with the completion maps.
- The base: a cuspidal representation of rank `r + 1` with unitary central
  character, regular algebraic and supercuspidal at `v` and `c(v)`.
- The conclusion: every unitary isobaric datum over `E` that is a weak base
  change of this cuspidal representation has, at `w`, the total
  supercuspidal support `Ch r π`, for every supercuspidal class `π` over
  `S.base` attached to the base at `v`. The support counts all constituents
  with their multiplicities.

The statement makes no regular-algebraicity or supercuspidality assumption
upstairs. Its vocabulary of local components and supercuspidal support of
isobaric data is defined in the module `Automorphic/IsobaricLocalSupport`,
in the Library at commit `d26f6985`. It defines when a cuspidal class has
a given p-adic local component and a given supercuspidal class at a finite
place (`CuspidalOperatorRealization.IsoClass.HasPadicLocalComponent` and
`HasPadicSupercuspidalClass`), the supercuspidal support of an isobaric
datum at a finite place (`IsobaricData.HasLocalSupercuspidalSupport`), and
`Correspondence.supercuspidalSupportDatum`. Besides two lemmas on ranks,
it states and proves no proposition. The restricted III.5.1 uses that
vocabulary and (I3), which stays unchanged; (I3) was not in the Library at
commit `86dbe494` and is at commit `24390f9f`. Keeping the chosen map and
its weak-law conjunct of the restricted III.5.1 recovers
`LocalCyclicBaseChangeStatement`. The restricted III.5.1 statement was
published at `95d37e11`. It is an input of E3, not a proof of E3 or (I4).
At `d6b462be`, both this statement and the rank-bounded (I4) that the
program starts from are in the Library.

The cyclic transfer statements B1–B3 (`CyclicStableDescentStatement`,
`CyclicRegularInductionStatement`, `CyclicRegularOrbitLiftStatement`)
assume a Hecke character `η` of `F` with `η.HasNormKernel E`. Nothing in
the Library at commit `d26f6985` produces one. The Library states
`Global.HeckeCharacter.CyclicNormKernelCharacterStatement` (module
`Global/Arithmetic/CyclicNormKernelCharacterStatement`). For cyclic `E/F`
there is such an `η`. Every such `η` has order `[E : F]`, and the Hecke
characters trivial on the norms from `E` are exactly the powers `η^i` with
`i < [E : F]`. Its proof was planned from the proved class-formation
reciprocity and `AdelicFunctoriality.isOpenMap_ideleClassNorm`. At commit
`8aede86c` the statement is in the Library, and it has no Library proof.
At commit `f050c0b1` the statement is proved:
`Global.HeckeCharacter.cyclicNormKernelCharacter` (module
`Global/Arithmetic/CyclicNormKernelCharacterProof`), for independent
universes `uF` and `uE`. Both the proof of statement 1 of the (I4) program and
Harris's Prop. 4.8 under the exact-stabilizer condition apply B1–B3 and so
need this character.

Premise 3. The route no longer needs this premise of the three-premise
theorem: the two-premise entry above uses its supercuspidal p-adic
variant, which is proved (see the end of this section). This section
records the general statement, its chain and the variant for reference.
`Conductor.ConductorExponentStatement` has no Library proof at commit
`314cfd1a`. The published `Conductor.conductorExponentStatement_of`
(module `Representation/Conductor/EssentialConductorReduction`) derives it
from five hypotheses. Since the sixteenth version, four of them follow
from published theorems:

- `Whittaker.MirabolicRestrictionInjectivityStatement` is proved by
  `Whittaker.mirabolicRestrictionInjectivity` (module
  `Representation/Whittaker/MirabolicRestrictionInjectivityProof`).
- `Conductor.TrivialCharacterEpsilonStatement` is proved by
  `Conductor.trivialCharacterEpsilon` (module
  `Representation/Conductor/TrivialCharacterEpsilonProof`).
- `Conductor.EssentialDualComparisonStatement` (JPSS 1981, (5.3)) is
  proved by `Conductor.essentialDualComparison` (module
  `Representation/Conductor/EssentialDualComparisonProof`), new since the
  sixteenth version. It applies
  `Conductor.essentialDualComparison_of_functionalEquation` (module
  `Representation/Conductor/EssentialDualComparisonBridge`) to mirabolic
  injectivity and to the corank-one spherical functional equation, which
  `Conductor.sphericalCorankOneFunctionalEquation` (module
  `Representation/Conductor/SphericalCorankOneFunctionalEquationProof`)
  proves for every nonarchimedean local field.
- `Conductor.ConductorMinimalityStatement` is proved by
  `Conductor.conductorMinimalityStatement` (module
  `Representation/Conductor/ConductorMinimalityProof`), new at commit
  `fab9caea`. The proof composes two published theorems.
  `Conductor.conductorMinimalityStatement_of_sphericalFunctionalEquation`
  (module `Representation/Conductor/ConductorMinimalityReduction`) derives
  it from `Conductor.SphericalLaurentFunctionalEquationStatement` and
  mirabolic injectivity. `Conductor.sphericalLaurentFunctionalEquation`
  (module
  `Representation/Conductor/SphericalLaurentFunctionalEquationProof`), new
  since the sixteenth version, proves that statement with no hypotheses.
  It applies
  `Conductor.sphericalLaurentFunctionalEquation_of_corankOne_of_laurent`
  (module
  `Representation/Conductor/SphericalLaurentFunctionalEquationReduction`)
  to the corank-one functional equation and to the published
  `Conductor.sphericalCorankOneLaurent` (module
  `Representation/Conductor/SphericalCorankOneLaurentProof`).

The fifth hypothesis, `Conductor.EssentialVectorExistence` (defined in the
reduction module; the existence half of Jacquet 2012, Theorem 1), is the
only one left. A search of the Lean sources at commit `544dba09` found no
unconditional proof of it. It is part of the first conjunct,
`Conductor.EssentialVectorStatement`, of
`Conductor.EssentialConductorStatement`.

Published theorems derive `EssentialVectorExistence` from the generation
statement `Conductor.OrderedUnramifiedCorankOneGenerationStatement`
(module
`Representation/Conductor/OrderedUnramifiedCorankOneGenerationStatement`).
Its Markdown attributes it to Jacquet 2012, Lemma 3, which quotes
Jacquet–Piatetski-Shapiro–Shalika 1983, where it is part of the
Proposition of §(9.4) (printed p. 458, displays (3)–(4)), which uses
§(8.4). For a generic representation π of `GL_(n+2)(F)` with L-polynomial
`P`, and an unramified principal series `I(x)` of `GL_(n+1)(F)` whose
parameters have nondecreasing norms, it says that a finite sum of
corank-one integrals, multiplied by `∏_i P(x_i q^(-s))`, equals 1 on a
right half-plane. `Conductor.sphericalLFactorGeneration_of_generation`
(module `Representation/Conductor/SphericalLFactorGenerationAssembly`)
derives `Conductor.SphericalLFactorGenerationStatement` from it, and
`Conductor.exists_isEssentialVector_of_jpss` (module
`Representation/Conductor/EssentialExistenceReduction`) gives an essential
vector of one representation from the conclusions of
`SphericalLFactorGenerationStatement` for that representation. Applied to
every representation, these give `EssentialVectorExistence`.

Separate Lean checks, not in the Library, compose these published theorems
in one module. Its theorem `conductorExponent_of_essentialVector_check`
proves `ConductorExponentStatement.{uF, uV}` from
`EssentialVectorExistence.{uF, uV}` alone, and its theorem
`conductorExponent_of_generation_check` proves it from
`OrderedUnramifiedCorankOneGenerationStatement.{uF, uV}` alone. The module
compiles at commit `544dba09` with 0 errors and 0 warnings. For each of
the two theorems, the declaration inspection lists only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

The proofs on this chain, as of 15 November 2026:

- `ConductorMinimalityStatement` is proved as a theorem of its own; see
  the list above.
- `SphericalLFactorGenerationStatement` has no proof. With
  `exists_isEssentialVector_of_jpss`, a proof would give
  `EssentialVectorExistence`. The generation statement is the last open
  input of such a proof.
- On 13 November 2026 the operator deferred the generation statement: the
  ordered-unramified L-product for generic π (JPSS 1983, (9.4) and (8.4))
  and the classification batch for (9.4) and (8.4) are out of scope until
  the operator decides. On 15 November 2026 the operator kept this
  deferral (Option C): `OrderedUnramifiedCorankOneGenerationStatement` is
  not to be proved, and the all-field port of the (9.4)/(8.4)
  classification batch is not to be started, until the operator decides on
  full generality; the route uses the supercuspidal p-adic variant below
  instead.

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

On 15 November 2026 the operator approved a variant of premise 3
restricted to supercuspidal representations over p-adic fields, and a
reduction statement for the three-premise theorem with that variant in
place of premise 3, with conditions: the statements go into new modules;
their Markdown cites JPSS 1981, Théorème (5.1), and JPSS 1983, Theorem
(2.7) and §(8.1); the general premise 3 and the deferral above stay
unchanged. Both statements are in the Library at commit `fab9caea`:

- `Conductor.SupercuspidalPadicConductorExponentStatement` (module
  `Representation/Conductor/SupercuspidalPadicConductorExponentStatement`).
  It is `ConductorExponentStatement` for the field `K.Carrier` of a p-adic
  field `K`, with the added hypothesis `GeneralLinear.IsSupercuspidal π`.
  It gives `K.Carrier` its canonical topology, valuation and local-field
  structure, as the route's call site does. The canonical structures were
  chosen because two published results that the planned proof needs are
  stated for them: `RankinSelberg.supercuspidalUnequalRankLFactor` (JPSS
  1983, §(8.1), Proposition (i)) and `Langlands.supercuspidalKirillov`.
- `Henniart.Extension.SupercuspidalCorrespondenceHenniartSupercuspidalConductorStatement`
  (module
  `Correspondence/HenniartSupercuspidalConductorReductionStatement`). It
  is the published three-premise statement with premise 3 replaced by the
  variant. It imports the variant's module.

A separate Lean check, not in the Library, proves that
`ConductorExponentStatement` implies the variant. It also proves that the
variant gives the conclusion of
`genericConductor_isNewvectorConductor_of_conductorExponentStatement` for
a supercuspidal representation, with the instances of
`GenericEpsilonConductor`, with 0 errors.

The variant is proved: `Conductor.supercuspidalPadicConductorExponent`
(module
`Representation/Conductor/SupercuspidalPadicConductorExponentProof`; in
the Library at commit `72480b70`) proves
`SupercuspidalPadicConductorExponentStatement.{uF, uV}` at independent
universes. Its Markdown describes the proof. Rank one is Tate's local
theory (the published `GodementJacquet.localTateConductor` with
`Conductor.conductorExponent_rankOne_of_localTate`). In rank at least 2
the proof follows the published `Conductor.conductorExponentStatement_of`.
The existence of essential vectors is supplied for supercuspidal
representations by the helper
`SupercuspidalPadic.exists_isEssentialVector` (module
`Representation/Conductor/SupercuspidalPadicEssentialExistence`), which
uses the fact that a supercuspidal representation has L-factor 1. It uses
neither `Conductor.EssentialVectorExistence` nor the deferred generation
statement. The reduction is proved as well, so the supercuspidal
correspondence follows from premises 1 and 2 alone.

Both are proved:

- `Conductor.SupercuspidalPadicConductorExponentStatement`, by the proof
  above;
- `Henniart.Extension.SupercuspidalCorrespondenceHenniartSupercuspidalConductorStatement`,
  by adapting the published route theorems in new modules; the proof is in
  the Library since commit `a98af0ff` (see "Published: the two-premise
  entry").

So the supercuspidal correspondence is to be assembled by applying the
theorem of the two-premise entry to proofs of candidate existence, of
numerical surjectivity and of the variant. The variant and the reduction
itself are proved. The proof of numerical surjectivity uses the variant at
arbitrary universes, which its proof provides, and the finiteness of
supercuspidal orbit strata, whose proof is in the Library (premise 2
above).

The proof of numerical surjectivity also uses the conductor finiteness of
supercuspidal classes, the second hypothesis of `numericalOrbitReduction`
under premise 2 above. A separate Lean check, not in the Library, proves
that the variant implies this hypothesis. The check obtains a nontrivial
additive character from `padicUnitaryAdditiveCharacterExists`, scales it
to conductor `O` by `UnramifiedUnitary.exists_scale_hasIntegerConductor`,
and gets genericity from
`SupercuspidalLFactorCharacterization.isGeneric_of_isSupercuspidal`. It
then applies the variant and
`Extension.firstFixedLevel_eq_of_isNewvectorConductor`. With
`numericalOrbitReduction`, it derives `NumericalSurjectivityStatement`
from `NumericalOrbitCountStatement` and the variant. It compiles at commit
`fab9caea` with 0 errors and 0 warnings. The declaration inspection lists
only the axioms `propext`, `Classical.choice` and `Quot.sound`. The same
code was compiled a second time, separately, with the same result.

The Library proves the two conjuncts of
`Conductor.OrderedUnramifiedWhittakerStatement` (module
`Representation/Conductor/OrderedUnramifiedWhittakerStatement`), the two
assertions about unramified principal series that the statement's
docstring attributes to Jacquet's corrected essential-vector argument
(Jacquet 2012, Lemmas 1 and 2).
`Conductor.orderedUnramifiedSphericalCyclicity` (module
`Representation/Conductor/OrderedUnramifiedSphericalCyclicity`) proves
`OrderedUnramifiedSphericalCyclicityStatement`: the normalized spherical
section generates the whole principal series when the norms of the
parameters are nondecreasing.
`Conductor.orderedUnramifiedWhittakerRealization` (module
`Representation/Conductor/OrderedUnramifiedWhittakerProof`) proves
`OrderedUnramifiedWhittakerRealizationStatement`: there is a nonzero
inverse-character functional with injective coefficient map that sends the
spherical section to the explicit spherical Whittaker function. Both
theorems hold for every nonarchimedean local field, at every field
universe.

## Operator decisions of 16 November 2026

The operator made six decisions on 16 November 2026. The other
recommendations of the operator's plan note are guidance, not decisions.

1. The numerical step: the proof of numerical surjectivity follows Option
   II; see premise 2 above.
2. Proof programs for the inputs of Option II: simple types and (I1), the
   trace formula and (I3), the Galois side and E1a, and Laumon's E1b; see
   premise 2 above.
3. The port of the NYLL library is stopped. Its three targets, the
   conjuncts `FiniteAbelianReciprocity`, `FiniteAbelianNormTransfer` and
   `FiniteAbelianRestriction` of
   `LocalClassField.FiniteAbelianReciprocityTheorems` (module
   `ClassFieldTheory/Local/FiniteReciprocityStatement`), follow from the
   Library's own finite Artin symbol. The port modules already in the
   Library stay there; the port is not to be reopened (plan note, Section
   5.1). Since commit `b369a8f2` the Library proves the conjunction as
   `LocalClassField.finiteAbelianReciprocityTheorems` (module
   `ClassFieldTheory/Local/FiniteReciprocityProof`). The proof combines
   the type-zero proofs and universe transports of published port modules
   under `ClassFieldTheory/Local/NYLL/`. Its Markdown says that its import
   closure contains no module under `Langlands/NYLL/`. No other Library
   module uses the conjunction.
4. Harris's Prop. 4.8 is restated under the exact-stabilizer condition;
   the present formulation stays as the fallback. See input 1 of premise 1
   above.
5. Group F of the plan note (arithmetic tools). The Library's
   `ChebotarevPrimeRealizationStatement` is to be proved by turning the
   audited private adaptation of the Chebotarev closure of the Anthropic
   FLT repository (Library note
   `notes/reuse/anthropic-chebotarev-audit.md`) into a port, and
   `FiniteGaloisFrobeniusRigidityStatement` and
   `ChebotarevRigidityStatement` are to be derived from it. How the five
   clauses of `FiniteAbelianClassFieldStatement` are to be obtained was to
   be decided by listing their consumers and auditing NYLL's global class
   field theory. The operator's decision on that audit, of 17 November
   2026, defers this statement; see item 2 of the next section.
   `FiniteGaloisFrobeniusRigidityStatement` is to be derived from
   `ChebotarevPrimeRealizationStatement` and the finite character theorem.
   By the plan note (Section 2.6), the route uses Chebotarev's theorem to
   pass from equal Frobenius traces at almost all places to isomorphic
   semisimple Galois representations and to choose auxiliary primes. At
   commit `ab9053b1` `ChebotarevPrimeRealizationStatement` is proved:
   `chebotarevPrimeRealizationStatement :
   ChebotarevPrimeRealizationStatement.{u, v}` (module
   `Global/Arithmetic/ChebotarevPrimeRealizationProof`). At commit
   `d26f6985` `FiniteGaloisFrobeniusRigidityStatement` is proved too:
   `finiteGaloisFrobeniusRigidityStatement :
   FiniteGaloisFrobeniusRigidityStatement.{u, v, w, z}` (module
   `Global/Arithmetic/FiniteGaloisFrobeniusRigidityProof`), from
   `chebotarevPrimeRealizationStatement`. `ChebotarevRigidityStatement`
   had no Library proof at commit `d26f6985`. At commit `8aede86c` it is
   proved: `chebotarevRigidityStatement : ChebotarevRigidityStatement.{u,
   v, w, z}` (module `Global/Arithmetic/ChebotarevRigidityProof`) is the
   pair of the two conjunct proofs above. So the three targets named in
   this item are Library theorems.
6. Six planned proofs whose targets are already Library theorems were
   dropped; none of these targets is named elsewhere in this note.

## Operator decisions of 17 November 2026

The operator made two decisions on 17 November 2026 that bear on the route
as a whole; they are listed below. The operator also ruled on three
questions of design of the exact-stabilizer branch (the bridge, standard
B6 and R2 rulings). They concern only the exact-stabilizer branch of
Harris's Prop. 4.8 and are recorded under input 1 of premise 1.

1. The proof of input (I4) of premise 2. The operator chose Option (a): a
   proof program of its own within the route of this note. Its target, its
   three statements and the statements it takes as given are described under premise
   2 above ("Input (I4): the proof program").
2. Interface F of the plan note (global class field theory). The operator
   deferred it. The Library's audit note
   `notes/reuse/nyll-global-cft-audit.md` (Section 7.1) records the
   decision in full. For this route it means the following.
   - Nothing from NYLL's global class field theory is imported now, and
     `Langlands.Global.FiniteAbelianClassFieldStatement` (module
     `Global/Arithmetic/ClassFieldStatement`) stays unproved; it and
     `Langlands.Global.ArtinNormComparisonStatement` (module
     `Global/Arithmetic/ArtinNormStatement`) are off the route. Neither
     statement is a hypothesis of a theorem of the composite below.
   - What reopens F: a statement on the route that needs the
     Frobenius-normalized idelic Artin map itself. In particular, F
     reopens if a proof of
     `ClassFieldTheory.Global.RelativeWeilGroup.WeakEquivalenceRigidityStatement`
     (module `Automorphic/AssociatedUniquenessStatement`; Henniart 2000,
     Section 2.2) enters the route. Then the lemmas U and R of the audit
     note (Section 6.2), which need no NYLL, come first, and after them
     only the clauses of F that this proof uses. The published
     `ClassFieldTheory.Global.cyclicHasseNorm` (module
     `ClassFieldTheory/Global/CyclicHasseNormProof`, at `7ae0d83b`) shows
     that, in a cyclic extension, a base-field unit whose principal idele
     is an idelic norm is already a field-unit norm. It does not construct
     the idelic Artin map, so its publication does not itself reopen F.
   - For the day F is wanted, the operator chose NYLL's head commit
     `b9a2dddb` as a package dependency pinned by commit and content hash,
     once the Library has moved to the Mathlib commit that this head uses;
     a trial of that move is under way. Until then there is to be no
     adapted copy of NYLL and no light port.
   - The cyclic transfer statements B1–B3 assume a Hecke character `η`
     with `η.HasNormKernel E`. When the operator answered (17 November
     2026), the Library had no theorem that produced one. At the
     operator's instruction, the statement
     `Global.HeckeCharacter.CyclicNormKernelCharacterStatement` was added
     for it; see premise 2 above. At commit `f050c0b1` the Library proves
     it (`Global.HeckeCharacter.cyclicNormKernelCharacter`, module
     `Global/Arithmetic/CyclicNormKernelCharacterProof`). The openness of
     the idele-class norm image, which the operator also asked for, is
     already proved in the Library
     (`Global.AdelicFunctoriality.isOpenMap_ideleClassNorm`).

## Statements that left the route

The route no longer needs premise 3 of the three-premise theorem,
`Conductor.ConductorExponentStatement`: the two-premise entry uses its
supercuspidal p-adic variant, which is proved, and the reduction of the
two-premise entry is proved. Neither the general statement nor
`SphericalLFactorGenerationStatement` is on the route any more. The
operator's conditions of 15 November 2026 stay in force: the general
statement and the deferral of the generation statement stay unchanged
(premise 3 above). The statement remains the second conjunct of
`Conductor.EssentialConductorStatement`.

The seventh version listed premises 2 and 4 of
`supercuspidalCorrespondenceHenniartFiveInputs` as open. Both are now
proved, as described above. The seventh version also named an alternative
route to premise 4, through finite abelian conductor transport
(`LocalClassField.FiniteCharacterConductorTheorems`) and inflation of
conductors (`Ramification.Padic.FiniteGaloisConductorInflationStatement`).
The published proof does not use these statements, so the route no longer
needs them.

The sixth version listed refinement invariance of presentation conductors,
`∀ p K A,
Ramification.Padic.FiniteInertiaConductorRefinementStatement.{uF, max uF
uP} K A`, as its fourth premise. The published
`finiteInertiaConductorRefinement` proves it.

The fifth version of this note listed `∀ p K,
ConductorExponent.SpectralConductorStatement.{uF, uP} K` as its fifth
premise. The published `spectralConductorRankOneReduction` derives it from
refinement invariance and premise 4 of the five-premise theorem, both now
proved, so the route no longer needs it as an open input. At `7ae0d83b`
the same reduction and the two proofs also give the standalone theorem
`LocalFactor.ConductorExponent.spectralConductor` (module
`LocalFactor/SpectralConductorProof`), without added hypotheses and with
independent field and representation universes. The conductor laws that
the route suggested for it needed also stay off this route: additivity in
short exact sequences and conductors of induced representations. Of the
conductor clauses of
`Ramification.Padic.InertiaSurjectivityPresentationAndConductorIndependenceStatement`
(module `LocalFactor/Ramification/InertiaPresentationStatement`), the
route uses only clause 6, refinement invariance, which is stated on its
own as `FiniteInertiaConductorRefinementStatement` and proved by
`finiteInertiaConductorRefinement`. This note does not record the status
of the other clauses.

The fourth version listed
`Henniart.SupercuspidalCompactOpenFinitenessStatement.{uF, uA}`
(Bernstein–Zelevinsky 1976, Cor. 4.15, printed p. 41, in compact-open
form), and the third version listed
`RankinSelberg.EqualRankEpsilonCharacterChangeStatement.{uF, uA, 0}`. The
Library proves the p-adic case of the first
(`Henniart.CompactOpenFiniteness.padicSupercuspidalCompactOpenFiniteness`),
which is the only case the route uses, and the second
(`RankinSelberg.equalRankEpsilonCharacterChange`), as described above. The
Library statement of the first quantifies over every nonarchimedean local
field, including fields of positive characteristic. It has since been
proved in that generality (`Henniart.supercuspidalCompactOpenFiniteness`,
see premise 2 above).

## The composite

The unchanged five-theorem block and its axiom-inspection module rebuilt
at `d6b462be` with zero errors and warnings. An axiom-printing build at
the same commit records only `propext`, `Classical.choice` and
`Quot.sound` for each theorem.

The module below compiles at commit
`24390f9f6d7a3b7df9e5b9dd4d6e79e178c8ac85` with 0 errors and 0 warnings.
The check compiled the block verbatim as a separate module, together with
a second module that imports it and runs `#print axioms` on each of its
five theorems. For each theorem the output lists only the axioms
`propext`, `Classical.choice` and `Quot.sound`. The same block compiled in
the same way at commit `b0b4deb8c936156b61ecb9730f7ff1ebb8ff3f5c`, with
the same axioms for the five theorems. The Library changed no Lean file
between commits `b0b4deb8` and `24390f9f`. The block below differs from
the checked one only in its comments. The twenty-eighth version changed
the third theorem, which no longer assumes the reduction statement D,
added the fifth theorem and added the import of
`Langlands.Correspondence.HenniartCandidateExistenceExactStabilizerTCReductionProof`.
The twenty-seventh version's block, with four theorems, compiled in the
same way at commit `86dbe494`, with the same axioms for each theorem, and
was also checked at commits `7e12a30c` and `f050c0b1`. The twenty-sixth
version added the fourth theorem and its import. The first three theorems,
without that import, were checked at commits `f050c0b1` and `ba9d1e9a`, at
commit `8aede86c` for the twenty-fifth version and at commit `d26f6985`
for the twenty-fourth version. The twenty-fourth version corrected one
docstring of the module (local relative class formation is the third input
of `candidateExistenceReduction`, not the fifth); the block before that
correction was also checked at commit `d26f6985`. The block of the
twenty-third version was checked at commit `ab9053b1`, and that of the
twenty-second version at commit `b369a8f2`. At commit `fcb85a7e` the
twenty-first version was also checked by a declaration inspection of each
theorem, with the same axioms. To reproduce the check, save the block as a
module, save a second module that imports it and contains the five `#print
axioms` commands, and compile both. The module is a development check, not
a published proof.

The first theorem, `fullCorrespondence_of_henniartTwoInputs`, has the two
open premises as its hypotheses, in the order of the table. It applies the
published
`Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor` to
these two hypotheses and to the published
`Conductor.supercuspidalPadicConductorExponent`, and then the published
`fullCorrespondenceStatement_of_supercuspidalCorrespondence`. The eighth
to nineteenth versions had in its place the three-premise theorem
`fullCorrespondence_of_henniartThreeInputs`, which applied
`supercuspidalCorrespondenceHenniartThreeInputs` and also assumed the
general conductor exponent statement
`Conductor.ConductorExponentStatement`. The eighth version's proof applied
`supercuspidalCorrespondenceHenniartFiveInputs` with
`NonabelianSystem.exists_system` and
`SpectralConductor.commonClosureRankOneConductor` directly, before the
three-premise theorem was published. The seventh version's composite,
`fullCorrespondence_of_henniartFiveInputs`, also assumed premises 2 and 4
of the five-premise theorem. The sixth version's composite,
`fullCorrespondence_of_henniartRankOneInputs`, assumed refinement
invariance as well.

The second theorem, `fullCorrespondence_zero_of_henniartGlobalInputs`, was
added in the fourteenth version. Its conclusion is
`FullCorrespondenceStatement.{uF, uP, 0}`: the full correspondence with
the representation universe `uA` equal to `0`. It applies the first
theorem at `uA = 0`. It obtains premise 1 at these universes,
`CandidateExistenceStatement.{uF, uP, 0, uP, uF}`, from
`candidateExistenceReduction.{uF, uP, uS, uP, uF}`. The published
`localRelativeClassFormation.{0}` supplies that reduction's third input.
The other four inputs are hypotheses, at the universes that the reduction
requires: Harris's Prop. 4.8, Henniart's Thm 2.4, Lemme 2.8 and §3.8. The
universe `uS` is the reduction's third universe parameter; it occurs only
in these four hypotheses. Premise 2 is a hypothesis at `uA = 0`. Up to the
nineteenth version the theorem also assumed the general conductor exponent
statement at `uA = 0`. The theorem does not prove the target at an
arbitrary universe `uA`; that passage belongs to the proof of candidate
existence (see premise 1 above).

The third theorem, `fullCorrespondence_zero_of_henniartTCInputs`, has the
same conclusion and also applies the first theorem at `uA = 0`. It obtains
premise 1 at the same universes from the published proposition
`CandidateExistenceTCReductionStatement.{uF, uP, uS, uP, uF}` (statement D
above, module
`Correspondence/HenniartCandidateExistenceTCReductionStatement`), applied
to `localRelativeClassFormation.{0}` and to four hypotheses. It obtains
that proposition from the published adapter
`Henniart.candidateExistenceTCReductionStatement_of_exactStabilizer`
(module
`Correspondence/HenniartCandidateExistenceExactStabilizerReductionStatement`)
applied to the published
`Henniart.candidateExistenceExactStabilizerTCReduction` (module
`Correspondence/HenniartCandidateExistenceExactStabilizerTCReductionProof`).
The four hypotheses are Harris's Prop. 4.8 in its present Library form,
`Global.Harris.Proposition48Statement`, at the same universes as in the
second theorem, and the totally complex forms of Henniart's Thm 2.4, Lemme
2.8 and §3.8: `AssociatedSupercuspidalInductionTCStatement` (module
`Automorphic/AssociatedFactorTCStatement`) and
`RelativeCertifiedPoleComparisonsTCStatement` and
`HenniartCompositeMapTCStatement` (module
`Global/Factors/PoleComparisonTCStatement`). Premise 2 is a hypothesis at
`uA = 0`. Up to the twenty-seventh version the theorem had a further
hypothesis, `hD : CandidateExistenceTCReductionStatement.{uF, uP, uS, uP,
uF}`, statement D; the derivation above replaces it. Like the second
theorem, the third does not prove the target at an arbitrary universe
`uA`.

The fourth theorem,
`fullCorrespondence_zero_of_henniartExactStabilizerInputs`, was added in
the twenty-sixth version. It is the second theorem with Harris's Prop. 4.8
in its exact-stabilizer form: its first hypothesis is
`Global.Harris.Proposition48ExactStabilizerStatement.{uF, 0, 0, 0, uS}`
(the restated proposition, module
`Global/Arithmetic/HarrisProposition48ExactStabilizerStatement`) instead
of `Global.Harris.Proposition48Statement` at the same universes. Its other
hypotheses and its conclusion are those of the second theorem. It obtains
premise 1 at the same universes from the published
`candidateExistenceExactStabilizerReduction.{uF, uP, uS, uP, uF}` (module
`Correspondence/HenniartCandidateExistenceExactStabilizerReductionProof`),
again with `localRelativeClassFormation.{0}` as the third input. The same
module as the restated proposition proves
`proposition48ExactStabilizerStatement_of_proposition48Statement`, so the
first hypothesis of the fourth theorem follows from that of the second.
Like the second theorem, the fourth does not prove the target at an
arbitrary universe `uA`.

The fifth theorem,
`fullCorrespondence_zero_of_henniartExactStabilizerTCInputs`, was added in
the twenty-eighth version. It is the third theorem with Harris's Prop. 4.8
in its exact-stabilizer form: its first hypothesis is
`Global.Harris.Proposition48ExactStabilizerStatement.{uF, 0, 0, 0, uS}`
instead of `Global.Harris.Proposition48Statement` at the same universes.
Its other hypotheses, the totally complex forms of Thm 2.4, Lemme 2.8 and
§3.8 and premise 2 at `uA = 0`, and its conclusion are those of the third
theorem. It obtains premise 1 at the same universes directly from the
published `candidateExistenceExactStabilizerTCReduction.{uF, uP, uS, uP,
uF}`, with `localRelativeClassFormation.{0}` as the third input. As for
the fourth theorem,
`proposition48ExactStabilizerStatement_of_proposition48Statement` shows
that the first hypothesis of the fifth theorem follows from that of the
third. Like the second theorem, the fifth does not prove the target at an
arbitrary universe `uA`.

```lean
import Langlands.Correspondence.FullCorrespondenceReduction
import Langlands.Correspondence.HenniartSupercuspidalConductorReductionProof
import Langlands.Representation.Conductor.SupercuspidalPadicConductorExponentProof
import Langlands.Correspondence.HenniartCandidateExistenceReductionProof
import Langlands.Correspondence.HenniartCandidateExistenceTCReductionStatement
import Langlands.ClassFieldTheory.Local.LocalRelativeClassFormationProof
import Langlands.Correspondence.HenniartCandidateExistenceExactStabilizerReductionProof
import Langlands.Correspondence.HenniartCandidateExistenceExactStabilizerTCReductionProof

namespace Langlands.Correspondence

universe uF uP uA uS

open Langlands.Henniart LocalFactor in
/-- The full correspondence from the two premises of Henniart's route that the Library does
not prove: candidate existence and numerical surjectivity. The conductor premise is supplied
in its supercuspidal p-adic form by the published `Conductor.supercuspidalPadicConductorExponent`,
through the published `supercuspidalCorrespondenceHenniartSupercuspidalConductor`. -/
theorem fullCorrespondence_of_henniartTwoInputs
    (hCE : CandidateExistenceStatement.{uF, uP, uA, uP, uF})
    (hnum : NumericalSurjectivityStatement.{uF, uP, uA}) :
    FullCorrespondenceStatement.{uF, uP, uA} :=
  fullCorrespondenceStatement_of_supercuspidalCorrespondence
    (Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor.{uF, uP, uA} hCE hnum
      Conductor.supercuspidalPadicConductorExponent.{uF, uA})

open Langlands.Henniart LocalFactor in
/-- Universe-`0` variant: with automorphic carrier universe `0`, candidate existence is
replaced by the other four of the five inputs of the proved
`candidateExistenceReduction`. Its third input, local relative class formation, is the
published theorem
`ClassFieldTheory.Local.localRelativeClassFormation`. -/
theorem fullCorrespondence_zero_of_henniartGlobalInputs
    (hHarris : Global.Harris.Proposition48Statement.{uF, 0, 0, 0, uS})
    (hasi : ClassFieldTheory.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionStatement.{0, uP, uS, uS})
    (hpole : Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement.{0, uP, uS})
    (hcomp : Global.PoleComparison.HenniartCompositeMapStatement.{0, uF, uP, uS, uP})
    (hnum : NumericalSurjectivityStatement.{uF, uP, 0}) :
    FullCorrespondenceStatement.{uF, uP, 0} :=
  fullCorrespondence_of_henniartTwoInputs.{uF, uP, 0}
    (candidateExistenceReduction.{uF, uP, uS, uP, uF} hHarris hasi
      ClassFieldTheory.Local.localRelativeClassFormation.{0} hpole hcomp)
    hnum

open Langlands.Henniart LocalFactor in
/-- Totally complex variant: candidate existence from Harris's Prop. 4.8 and the totally
complex forms of Henniart's Thm 2.4, Lemme 2.8 and §3.8. The totally complex reduction
statement `CandidateExistenceTCReductionStatement` is derived, by the published
`candidateExistenceTCReductionStatement_of_exactStabilizer`, from the published
`candidateExistenceExactStabilizerTCReduction`. -/
theorem fullCorrespondence_zero_of_henniartTCInputs
    (hHarris : Global.Harris.Proposition48Statement.{uF, 0, 0, 0, uS})
    (hasi : ClassFieldTheory.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionTCStatement.{0, uP, uS, uS})
    (hpole : Global.PoleComparison.RelativeCertifiedPoleComparisonsTCStatement.{0, uP, uS})
    (hcomp : Global.PoleComparison.HenniartCompositeMapTCStatement.{0, uF, uP, uS, uP})
    (hnum : NumericalSurjectivityStatement.{uF, uP, 0}) :
    FullCorrespondenceStatement.{uF, uP, 0} :=
  fullCorrespondence_of_henniartTwoInputs.{uF, uP, 0}
    (candidateExistenceTCReductionStatement_of_exactStabilizer.{uF, uP, uS, uP, uF}
      candidateExistenceExactStabilizerTCReduction.{uF, uP, uS, uP, uF}
      hHarris hasi ClassFieldTheory.Local.localRelativeClassFormation.{0} hpole hcomp)
    hnum

open Langlands.Henniart LocalFactor in
/-- Exact-stabilizer variant: as `fullCorrespondence_zero_of_henniartGlobalInputs`, with
Harris's Prop. 4.8 taken in its exact-stabilizer form
`Global.Harris.Proposition48ExactStabilizerStatement`, through the published
`candidateExistenceExactStabilizerReduction`. -/
theorem fullCorrespondence_zero_of_henniartExactStabilizerInputs
    (hHarris : Global.Harris.Proposition48ExactStabilizerStatement.{uF, 0, 0, 0, uS})
    (hasi : ClassFieldTheory.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionStatement.{0, uP, uS, uS})
    (hpole : Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement.{0, uP, uS})
    (hcomp : Global.PoleComparison.HenniartCompositeMapStatement.{0, uF, uP, uS, uP})
    (hnum : NumericalSurjectivityStatement.{uF, uP, 0}) :
    FullCorrespondenceStatement.{uF, uP, 0} :=
  fullCorrespondence_of_henniartTwoInputs.{uF, uP, 0}
    (candidateExistenceExactStabilizerReduction.{uF, uP, uS, uP, uF} hHarris hasi
      ClassFieldTheory.Local.localRelativeClassFormation.{0} hpole hcomp)
    hnum

open Langlands.Henniart LocalFactor in
/-- Totally complex exact-stabilizer variant: as `fullCorrespondence_zero_of_henniartTCInputs`,
with Harris's Prop. 4.8 taken in its exact-stabilizer form
`Global.Harris.Proposition48ExactStabilizerStatement`, through the published
`candidateExistenceExactStabilizerTCReduction`. -/
theorem fullCorrespondence_zero_of_henniartExactStabilizerTCInputs
    (hHarris : Global.Harris.Proposition48ExactStabilizerStatement.{uF, 0, 0, 0, uS})
    (hasi : ClassFieldTheory.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionTCStatement.{0, uP, uS, uS})
    (hpole : Global.PoleComparison.RelativeCertifiedPoleComparisonsTCStatement.{0, uP, uS})
    (hcomp : Global.PoleComparison.HenniartCompositeMapTCStatement.{0, uF, uP, uS, uP})
    (hnum : NumericalSurjectivityStatement.{uF, uP, 0}) :
    FullCorrespondenceStatement.{uF, uP, 0} :=
  fullCorrespondence_of_henniartTwoInputs.{uF, uP, 0}
    (candidateExistenceExactStabilizerTCReduction.{uF, uP, uS, uP, uF} hHarris hasi
      ClassFieldTheory.Local.localRelativeClassFormation.{0} hpole hcomp)
    hnum

end Langlands.Correspondence
```

## Statements off this route

The specification coverage note lists two statements that the reduction
above does not use. At `7ae0d83b` `Correspondence.assemblyExtends` (module
`Correspondence/AssemblyExtendsProof`) proves
`Correspondence.AssemblyExtendsStatement` (module
`Correspondence/AssemblyRelation`) without added hypotheses and with
independent field, parameter and representation universes. It uses the
zero-monodromy witness and the uniqueness of the assembled class. The
other statement, `Correspondence.FullCorrespondenceRestrictionStatement`
(module `Correspondence/FullSpecification`), had no proof on 12 November
2026.

## Duplicate declaration names: resolved

The first version of this note recorded that a composite import failed
because published modules declared the same instance names without
importing each other, for example
`Langlands.Correspondence.instTopologicalSpaceCarrier_5`. The repeated
declarations were renamed; the renames have been in the Library since
commit `3f9691717b5fba9a8561abf028ae957f63bdf0dd`. The scan for them is
described in
`Langlands/Correspondence/AssemblyLCharacterizationReduction.md`, section
"How the names were checked". The composite above compiles without private
renamed copies.

## Present status of the statements named in this note

The sections above describe the Library at the commits they name. This section gives, for every statement (a Prop-valued `…Statement` declaration) that the note names, its status in the Library as it is now. A statement counts as proved when a theorem of the Library has the statement itself as its type; it counts as derived from further statements when the Library only has theorems that assume other statements (reductions, `…_of_…` theorems, equivalences). Statements declared in two files were checked against the namespace that the note names. Of the 214 statements, 102 are proved, 30 are derived only from further statements and 82 have no proof.

| Statement | Status in the Library |
| --- | --- |
| `AdjointExactnessStatement` | proved by `adjointExactness` (`BushnellKutzko/AdjointExactnessProof`) |
| `Correspondence.AssemblyExtendsStatement` | proved by `assemblyExtends` (`Correspondence/AssemblyExtendsProof`) |
| `RelativeWeilGroup.AssociatedCuspidalFactorReductionTCStatement` | proved by `associatedCuspidalFactorReductionTC` (`Automorphic/AssociatedCuspidalFactorReductionTC`) |
| `RelativeWeilGroup.AssociatedGammaReductionTCStatement` | proved by `associatedGammaReductionTC` (`Automorphic/AssociatedGammaTCReductionProof`) |
| `BushnellKutzkoLabelCountStatement` | proved by `bushnellKutzkoLabelCount` (`Correspondence/BushnellKutzkoLabelCountProof`) |
| `Henniart.CandidateExistenceExactStabilizerReductionStatement` | proved by `candidateExistenceExactStabilizerReduction` (`Correspondence/HenniartCandidateExistenceExactStabilizerReductionProof`) |
| `Henniart.CandidateExistenceExactStabilizerTCReductionStatement` | proved by `candidateExistenceExactStabilizerTCReduction` (`Correspondence/HenniartCandidateExistenceExactStabilizerTCReductionProof`) |
| `Henniart.CandidateExistenceReductionStatement` | proved by `candidateExistenceReduction` (`Correspondence/HenniartCandidateExistenceReductionProof`) |
| `Henniart.CandidateExistenceTCReductionStatement` | proved by `candidateExistenceTCReduction` (`Correspondence/HenniartCandidateExistenceTCReductionProof`) |
| `ChebotarevPrimeRealizationStatement` | proved by `chebotarevPrimeRealizationStatement` (`Global/Arithmetic/ChebotarevPrimeRealizationProof`) |
| `ChebotarevRigidityStatement` | proved by `chebotarevRigidityStatement` (`Global/Arithmetic/ChebotarevRigidityProof`) |
| `CloseFieldsGaloisQuotientStatement` | proved by `closeFieldsGaloisQuotient` (`LocalFactor/Ramification/CloseFieldsGaloisQuotientProof`) |
| `LocalFactor.ComplexArchimedeanTateStatement` | proved by `complexArchimedeanTateStatement` (`LocalFactor/Archimedean/ComplexTateProof`) |
| `ComplexGenericStandardParameterStatement` | proved by `complexGenericStandardParameter` (`Representation/Archimedean/ComplexGenericStandardParameterProof`) |
| `ComplexLocalEqualFunctionalEquationStatement` | proved by `complexLocalEqualFunctionalEquation` (`Global/RankinSelberg/ComplexPlaceEqualFunctionalEquationProof`) |
| `ComplexLocalUnequalFunctionalEquationStatement` | proved by `complexLocalUnequalFunctionalEquation` (`Global/RankinSelberg/ComplexPlaceUnequalFunctionalEquationProof`) |
| `Conductor.ConductorMinimalityStatement` | proved by `conductorMinimalityStatement` (`Representation/Conductor/ConductorMinimalityProof`) |
| `Global.CuspidalArchimedeanParameterExistenceTCStatement` | proved by `cuspidalArchimedeanParameterExistenceTC` (`Automorphic/CuspidalArchimedeanParameterExistenceTC`) |
| `Automorphic.CuspidalArithmeticSpectralTransportStatement` | proved by `cuspidalArithmeticSpectralTransport` (`Automorphic/CuspidalArithmeticSpectralTransportProof`) |
| `CuspidalComplexParameterBridgeTCStatement` | proved by `cuspidalComplexParameterBridgeTC` (`Automorphic/CuspidalComplexParameterBridgeProof`) |
| `CuspidalPairAbsoluteConvergenceReductionStatement` | proved by `cuspidalPairAbsoluteConvergenceReduction` (`Global/Factors/CuspidalPairAbsoluteConvergenceProof`) |
| `Global.CuspidalPairFunctionalEquationReductionTCStatement` | proved by `cuspidalPairFunctionalEquationReductionTC` (`Global/Factors/CuspidalPairFunctionalEquationReductionTCProof`) |
| `CuspidalSelfPairContinuationStatement` | proved by `cuspidalSelfPairContinuation` (`Global/Factors/CuspidalSelfPairContinuationProof`) |
| `Global.HeckeCharacter.CyclicNormKernelCharacterStatement` | proved by `cyclicNormKernelCharacter` (`Global/Arithmetic/CyclicNormKernelCharacterProof`) |
| `CyclicNormLemmaStatement` | proved by `cyclicNormLemma` (`BaseChange/CyclicNormLemma`) |
| `CyclicTowerStatement` | proved by `cyclicTower` (`Correspondence/HenniartCyclicTowerProof`) |
| `RankinSelberg.EqualRankEpsilonCharacterChangeStatement` | proved by `equalRankEpsilonCharacterChange` (`Representation/RankinSelberg/EqualRankEpsilonCharacterChangeProof`) |
| `EqualSemilocalFactorizationReductionTCStatement` | proved by `equalSemilocalFactorizationReductionTC` (`Global/RankinSelberg/EqualSemilocalFactorizationReductionTC`) |
| `Conductor.EssentialDualComparisonStatement` | proved by `essentialDualComparison` (`Representation/Conductor/EssentialDualComparisonProof`) |
| `Langlands.Global.FiniteAbelianClassFieldStatement` | proved by `finiteAbelianClassField` (`Global/Arithmetic/ClassFieldProof`) |
| `Ramification.Padic.FiniteGaloisConductorInflationStatement` | proved by `finiteGaloisConductorInflation` (`LocalFactor/Ramification/InflationProof`) |
| `FiniteGaloisFrobeniusRigidityStatement` | proved by `finiteGaloisFrobeniusRigidityStatement` (`Global/Arithmetic/FiniteGaloisFrobeniusRigidityProof`) |
| `FiniteInertiaConductorRefinementStatement` | proved by `finiteInertiaConductorRefinement` (`LocalFactor/Ramification/InertiaConductorRefinementProof`) |
| `FundamentalStratumLevelStatement` | proved by `fundamentalStratumLevel` (`BushnellKutzko/FundamentalStratumLevelProof`) |
| `GeneralLinearCuspFormLocalVanishingStatement` | proved by `generalLinearCuspFormLocalVanishing` (`TraceFormula/GeneralLinearCuspFormLocalVanishingProof`) |
| `Global.HarrisDatumCharacterRealizationExactStabilizerStatement` | proved by `harrisDatumCharacterRealizationExactStabilizer` (`Global/Arithmetic/HenniartHarrisDatumExactStabilizerProof`) |
| `HenniartCompositeFactorStatement` | proved by `henniartCompositeFactor` (`Global/Factors/HenniartCompositeFactorProof`) |
| `HenniartCompositeOperationStatement` | proved by `henniartCompositeOperation` (`Global/Factors/HenniartCompositeOperationProof`) |
| `Global.HenniartGlobalizationExactStabilizerReductionStatement` | proved by `henniartGlobalizationExactStabilizerReduction` (`Global/Arithmetic/HenniartGlobalizationExactStabilizerProof`) |
| `HerbrandPsiTruncationStatement` | proved by `herbrandPsiTruncation` (`LocalFactor/Ramification/Herbrand/KummerTruncationProof`) |
| `Ramification.Padic.InertiaSurjectivityPresentationAndConductorIndependenceStatement` | proved by `inertiaSurjectivityPresentationAndConductorIndependence` (`LocalFactor/Ramification/InertiaPresentationProof`) |
| `KummerStageWeilQuotientStatement` | proved by `kummerStageWeilQuotient` (`LocalFactor/Ramification/Herbrand/KummerStageWeilQuotientProof`) |
| `KummerStepHerbrandPsiStatement` | proved by `kummerStepHerbrandPsi` (`LocalFactor/Ramification/Herbrand/KummerStepHerbrandPsiProof`) |
| `KummerStepUpperSupStatement` | proved by `kummerStepUpperSup` (`LocalFactor/Ramification/Herbrand/KummerStepUpperSupProof`) |
| `KummerTowerHerbrandPsiStatement` | proved by `kummerTowerHerbrandPsi` (`LocalFactor/Ramification/Herbrand/KummerTowerHerbrandPsiProof`) |
| `KummerTowerLimitUpperSupStatement` | proved by `kummerTowerLimitUpperSup` (`LocalFactor/Ramification/Herbrand/KummerTowerLimitUpperSupProof`) |
| `KummerTowerUpperSupStatement` | proved by `kummerTowerUpperSup` (`LocalFactor/Ramification/Herbrand/KummerTowerUpperSupProof`) |
| `ClassFieldTheory.Local.LocalRelativeClassFormationStatement` | proved by `localRelativeClassFormation` (`ClassFieldTheory/Local/LocalRelativeClassFormationProof`) |
| `MinimalCriticalExponentStatement` | proved by `minimalCriticalExponent` (`BushnellKutzko/MinimalCriticalExponentProof`) |
| `Whittaker.MirabolicRestrictionInjectivityStatement` | proved by `mirabolicRestrictionInjectivity` (`Representation/Whittaker/MirabolicRestrictionInjectivityProof`) |
| `NormalizedLevelExistenceStatement` | proved by `normalizedLevelExistence` (`BushnellKutzko/NormalizedLevelExistenceProof`) |
| `NormalizedLevelTwistStatement` | proved by `normalizedLevelTwist` (`BushnellKutzko/NormalizedLevelTwistProof`) |
| `NormNeighbourhoodStatement` | proved by `normNeighbourhood` (`BaseChange/NormNeighbourhood`) |
| `Henniart.NumericalOrbitReductionStatement` | proved by `numericalOrbitReduction` (`Correspondence/HenniartNumericalReductionProof`) |
| `OrbitalIntegralPositivityStatement` | proved by `orbitalIntegralPositivity` (`BaseChange/OrbitalIntegralPositivity`) |
| `OrbitalMeasureExistenceStatement` | proved by `orbitalMeasureExistence` (`BaseChange/OrbitalMeasureExistence`) |
| `OrderedUnramifiedSphericalCyclicityStatement` | proved by `orderedUnramifiedSphericalCyclicity` (`Representation/Conductor/OrderedUnramifiedSphericalCyclicity`) |
| `OrderedUnramifiedWhittakerRealizationStatement` | proved by `orderedUnramifiedWhittakerRealization` (`Representation/Conductor/OrderedUnramifiedWhittakerProof`) |
| `PolarPartClosedFormulaStatement` | proved by `polarPartClosedFormula` (`Correspondence/HenniartPolarPartClosedFormulaProof`) |
| `PolarPartCountingIdentityStatement` | proved by `polarPartCountingIdentity` (`Correspondence/HenniartPolarPartCountingIdentityProof`) |
| `PolarPartTruncatedUniquenessStatement` | proved by `polarPartTruncatedUniqueness` (`Correspondence/HenniartPolarPartTruncatedUniquenessProof`) |
| `Proposition48AuxiliaryRankOneStatement` | proved by `proposition48AuxiliaryRankOne` (`Global/Arithmetic/HarrisProposition48AuxiliaryRankOneProof`) |
| `Proposition48ExactStabilizerAuxiliaryRankOneStatement` | proved by `proposition48ExactStabilizerAuxiliaryRankOne` (`Global/Arithmetic/HarrisProposition48ExactStabilizerAuxiliaryRankOneProof`) |
| `Proposition48ExactStabilizerDistinctnessStatement` | proved by `proposition48ExactStabilizerDistinctness` (`Global/Arithmetic/HarrisProposition48ExactStabilizerDistinctnessProof`) |
| `Proposition48ExactStabilizerDistinctnessTCStatement` | proved by `proposition48ExactStabilizerDistinctnessTC` (`Global/Arithmetic/HarrisProposition48ExactStabilizerDistinctnessTCProof`) |
| `Proposition48ExactStabilizerMackeyInheritanceStatement` | proved by `proposition48ExactStabilizerMackeyInheritance` (`Global/Arithmetic/HarrisProposition48ExactStabilizerMackeyProof`) |
| `Proposition48ExactStabilizerParameterUntwistStatement` | proved by `proposition48ExactStabilizerParameterUntwist` (`Global/Arithmetic/HarrisProposition48ExactStabilizerParameterUntwistProof`) |
| `Proposition48ExactStabilizerParityInheritanceStatement` | proved by `proposition48ExactStabilizerParityInheritance` (`Global/Arithmetic/HarrisProposition48ExactStabilizerParityInheritanceProof`) |
| `Proposition48IsobaricInvarianceStatement` | proved by `proposition48IsobaricInvariance` (`Global/Arithmetic/HarrisProposition48IsobaricInvarianceProof`) |
| `Proposition48MackeyStepStatement` | proved by `proposition48MackeyStep` (`Global/Arithmetic/HarrisProposition48MackeyStepProof`) |
| `Global.Harris.Proposition48RankOneStatement` | proved by `proposition48RankOne` (`Global/Arithmetic/HarrisProposition48RankOneProof`) |
| `Global.Harris.Proposition48ReductionStatement` | proved by `proposition48Reduction` (`Global/Arithmetic/HarrisProposition48ReductionProof`) |
| `Global.Harris.Proposition48ReductionTCStatement` | proved by `proposition48ReductionTC` (`Global/Arithmetic/HarrisProposition48ReductionTCProof`) |
| `RefinedStrataStatement` | proved by `refinedStrata` (`Correspondence/HenniartRefinedStrataProof`) |
| `RefinementStatement` | proved by `refinement` (`BushnellKutzko/RefinementProof`) |
| `RegularTransferStatement` | proved by `regularTransfer` (`BaseChange/RegularTransfer`) |
| `RelativeIsometryOperationStatement` | proved by `relativeIsometryOperation` (`Global/Factors/RelativeIsometryOperationProof`) |
| `SatakeCharacterStatement` | proved by `satakeCharacter` (`BaseChange/SatakeCharacter`) |
| `SimpleIntertwiningStatement` | proved by `simpleIntertwining` (`BushnellKutzko/SimpleIntertwiningProof`) |
| `LocalFactor.ConductorExponent.SpectralConductorStatement` | proved by `spectralConductor` (`LocalFactor/SpectralConductorProof`) |
| `Conductor.SphericalLaurentFunctionalEquationStatement` | proved by `sphericalLaurentFunctionalEquation` (`Representation/Conductor/SphericalLaurentFunctionalEquationProof`) |
| `SplitMatchingStatement` | proved by `splitMatching` (`BaseChange/SplitMatching`) |
| `StableTwistPairGammaMatchStatement` | proved by `stableTwistPairGammaMatchStatement` (`Automorphic/StableTwistGammaMatchProof`) |
| `StratumEquivalenceStatement` | proved by `stratumEquivalence` (`BushnellKutzko/StratumEquivalenceProof`) |
| `Henniart.SupercuspidalCompactOpenFinitenessStatement` | proved by `supercuspidalCompactOpenFiniteness` (`Correspondence/SupercuspidalCompactOpenFinitenessProof`) |
| `Henniart.Extension.SupercuspidalCorrespondenceHenniartSupercuspidalConductorStatement` | proved by `supercuspidalCorrespondenceHenniartSupercuspidalConductor` (`Correspondence/HenniartSupercuspidalConductorReductionProof`) |
| `Henniart.Extension.SupercuspidalCorrespondenceHenniartThreeInputsStatement` | proved by `supercuspidalCorrespondenceHenniartThreeInputs` (`Correspondence/HenniartCorrespondenceThreeInputs`) |
| `Henniart.SupercuspidalOrbitStratumFinitenessStatement` | proved by `supercuspidalOrbitStratumFiniteness` (`Correspondence/HenniartOrbitStratumFinitenessProof`) |
| `Conductor.SupercuspidalPadicConductorExponentStatement` | proved by `supercuspidalPadicConductorExponent` (`Representation/Conductor/SupercuspidalPadicConductorExponentProof`) |
| `SupercuspidalSwanLevelStatement` | proved by `supercuspidalSwanLevel` (`BushnellKutzko/SupercuspidalSwanLevelProof`) |
| `Henniart.SupercuspidalTwistSwanBoundReductionStatement` | proved by `supercuspidalTwistSwanBoundReduction` (`Correspondence/HenniartTwistSwanReductionProof`) |
| `SupercuspidalTwistSwanBoundStatement` | proved by `supercuspidalTwistSwanBound` (`Correspondence/HenniartTwistSwanProof`) |
| `TameCorestrictionStatement` | proved by `tameCorestriction` (`BushnellKutzko/TameCorestrictionProof`) |
| `Conductor.TrivialCharacterEpsilonStatement` | proved by `trivialCharacterEpsilon` (`Representation/Conductor/TrivialCharacterEpsilonProof`) |
| `TruncationGaloisQuotientStatement` | proved by `truncationGaloisQuotient` (`LocalFactor/Ramification/Herbrand/TruncationGaloisQuotientProof`) |
| `TruncationWeilRestrictionStatement` | proved by `truncationWeilRestriction` (`LocalFactor/Ramification/Herbrand/TruncationWeilRestrictionProof`) |
| `RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement` | proved by `unitaryGenericLPolynomialNonvanishing` (`Representation/RankinSelberg/UnitaryGenericLPolynomialNonvanishingProof`) |
| `UnitFundamentalLemmaStatement` | proved by `unitFundamentalLemma` (`BaseChange/UnitFundamentalLemma`) |
| `WeilArtinConductorExistenceStatement` | proved by `weilArtinConductorExistence` (`Correspondence/HenniartWeilArtinConductorExistenceProof`) |
| `WeilConductorCountStepStatement` | proved by `weilConductorCountStep` (`Correspondence/HenniartWeilConductorCountStepProof`) |
| `WeilRankOneCountStatement` | proved by `weilRankOneCount` (`Correspondence/HenniartWeilRankOneCountProof`) |
| `WeilUnramifiedDescentCountStatement` | proved by `weilUnramifiedDescentCount` (`Correspondence/HenniartWeilUnramifiedDescentCountProof`) |
| `ClassFieldTheory.Global.RelativeWeilGroup.AssociatedGammaStatement` | derived only from further statements, for example by `associatedGamma_of_inputs` (`Automorphic/AssociatedGammaFinal`) |
| `RelativeWeilGroup.AssociatedGammaTCStatement` | derived only from further statements, for example by `associatedGamma_of_inputs_tc` (`Automorphic/AssociatedGammaTCReductionProof`) |
| `ComplexEqualPlaceTestsStatement` | derived only from further statements, for example by `complexEqualPlaceTests_of_positive` (`Global/RankinSelberg/EqualWhittakerPositiveRankReduction`) |
| `ComplexUnequalNormalizedIntertwinerEquationStatement` | derived only from further statements, for example by `complexUnequalNormalizedFromCanonical` (`Global/RankinSelberg/ComplexLocalUnequalFromCanonical`) |
| `Conductor.ConductorExponentStatement` | derived only from further statements, for example by `conductorExponentStatement_of` (`Representation/Conductor/EssentialConductorReduction`) |
| `CuspidalEulerConstituentRecoveryStatement` | derived only from further statements, for example by `cuspidalEulerConstituentRecovery_of_powerTraceRecovery` (`Automorphic/Unramified/CuspidalSpectralRigidityReduction`) |
| `Global.CuspidalPairCompletedEquationTCStatement` | derived only from further statements, for example by `cuspidalPairCompletedEquationTC_of_completedEquation` (`Global/Factors/CuspidalPairPartialGammaTCReduction`) |
| `Global.CuspidalPairPartialGammaEquationTCStatement` | derived only from further statements, for example by `cuspidalPairPartialGammaEquationTC_of_partialGamma` (`Global/Factors/CuspidalPairPartialGammaTCReduction`) |
| `CuspidalPairPoleStatement` | derived only from further statements, for example by `cuspidalPairPole_of_covering_normalized_products` (`Global/Factors/CuspidalPairPoleEqualCover`) |
| `CuspidalSpectralRigidityTCStatement` | derived only from further statements, for example by `cuspidalSpectralRigidityTC_of_normalizedContinuation` (`Automorphic/Unramified/CuspidalSpectralRigidityTCPoleProfileReduction`) |
| `CyclicPrimeIsobaricBaseChangeTCStatement` | derived only from further statements, for example by `cyclicPrimeIsobaricBaseChangeTC_of_cuspidal` (`Automorphic/Unramified/CyclicPrimeIsobaricBaseChangeTCAssembly`) |
| `CyclicWeakInductionSupercuspidalStatement` | derived only from further statements, for example by `cyclicWeakInductionSupercuspidal_of_matching_at_completion` (`Automorphic/Unramified/CyclicInductionSupercuspidalReduction`) |
| `CyclicWeakInductionSupercuspidalTCStatement` | derived only from further statements, for example by `cyclicWeakInductionSupercuspidalTC_of_gammaOrder` (`Automorphic/Unramified/CyclicWeakInductionSelfPairGamma`) |
| `EqualInfiniteWhittakerTestStatement` | derived only from further statements, for example by `equalInfiniteWhittakerTest_of_local` (`Global/RankinSelberg/EqualInfiniteWhittakerSliceReduction`) |
| `EqualSemilocalEquationTCStatement` | derived only from further statements, for example by `equalSemilocalEquationTC_of_unrestricted` (`Global/Factors/CuspidalPairPartialGammaGlobalTCReduction`) |
| `EqualSemilocalFactorizationTCStatement` | derived only from further statements, for example by `equalSemilocalFactorizationTC_of_archimedeanSemilocalTheory` (`Global/RankinSelberg/EqualSemilocalFactorizationReductionTC`) |
| `Conductor.EssentialConductorStatement` | derived only from further statements, for example by `essentialConductorStatement_of` (`Representation/Conductor/EssentialConductorReduction`) |
| `Conductor.EssentialVectorStatement` | derived only from further statements, for example by `essentialVectorStatement_of_existence` (`Representation/Conductor/EssentialConductorReduction`) |
| `Langlands.Correspondence.FullCorrespondenceStatement` | derived only from further statements, for example by `fullCorrespondenceStatement_of_supercuspidalCorrespondence` (`Correspondence/FullCorrespondenceReduction`) |
| `HenniartGlobalizationStatement` | derived only from further statements, for example by `henniartGlobalization_of_inputs` (`Global/Arithmetic/HenniartGlobalizationReduction`) |
| `InfiniteWhittakerSliceModelStatement` | derived only from further statements, for example by `infiniteWhittakerSliceModel_of_positive` (`Global/RankinSelberg/EqualWhittakerPositiveRankReduction`) |
| `RankinSelberg.PairEpsilonExponentStatement` | derived only from further statements, for example by `pairEpsilonExponent_of_characterChange` (`Representation/RankinSelberg/PairEpsilonExponentProof`) |
| `Global.Harris.Proposition48ExactStabilizerStatement` | derived only from further statements, for example by `proposition48ExactStabilizerStatement_of_proposition48Statement` (`Global/Arithmetic/HarrisProposition48ExactStabilizerStatement`) |
| `Global.Harris.Proposition48Statement` | derived only from further statements, for example by `proposition48_of_hasSolution` (`Global/Arithmetic/HarrisProposition48ReductionProof`) |
| `RealEqualPlaceTestsStatement` | derived only from further statements, for example by `realEqualPlaceTests_of_positive` (`Global/RankinSelberg/EqualWhittakerPositiveRankReduction`) |
| `Conductor.SphericalLFactorGenerationStatement` | derived only from further statements, for example by `sphericalLFactorGeneration_of_ordered` (`Representation/Conductor/SphericalLFactorGenerationReduction`) |
| `SupercuspidalCorrespondenceStatement` | derived only from further statements, for example by `supercuspidalCorrespondenceStatement_of_localConverse_of_existence` (`Correspondence/SupercuspidalUniquenessFromConverse`) |
| `Henniart.SupercuspidalEpsilonConductorFinitenessStatement` | derived only from further statements, for example by `supercuspidalEpsilonConductorFiniteness_of_pairEpsilon` (`Correspondence/HenniartPadicConductorFinitenessProof`) |
| `TwistedCharacterRegularValuesStatement` | derived only from further statements, for example by `TwistedCharacterLocalIntegrabilityStatement.regularValues` (`BaseChange/TwistedCharacterLocalIntegrabilityStatement`) |
| `UnequalSemilocalEquationTCStatement` | derived only from further statements, for example by `unequalSemilocalEquationTC_of_unrestricted` (`Global/Factors/CuspidalPairPartialGammaGlobalTCReduction`) |
| `ArchimedeanFactorizationStatement` | no proof in the Library |
| `ArchimedeanFunctionalEquationStatement` | no proof in the Library |
| `ArchimedeanSemilocalTheoryStatement` | no proof in the Library |
| `Langlands.Global.ArtinNormComparisonStatement` | no proof in the Library |
| `AssociatedCuspidalFactorTCStatement` | no proof in the Library |
| `ClassFieldTheory.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionStatement` | no proof in the Library |
| `AssociatedSupercuspidalInductionTCStatement` | no proof in the Library |
| `AssociatedTemperedFactorTCStatement` | no proof in the Library |
| `BaseChangeSlopeStatement` | no proof in the Library |
| `Henniart.CandidateExistenceStatement` | no proof in the Library |
| `Henniart.CompatibleNumericalInjectionsStatement` | no proof in the Library |
| `ComplexLocalEqualMeromorphicEquationStatement` | no proof in the Library |
| `ComplexLocalEqualPrimalContinuationStatement` | no proof in the Library |
| `ComplexPlaceFunctionalEquationStatement` | no proof in the Library |
| `ComplexSemilocalTheoryStatement` | no proof in the Library |
| `CountingSurjectivityStatement` | no proof in the Library |
| `CuspidalArchimedeanPairRegularityStatement` | no proof in the Library |
| `CuspidalPairBoundaryNonvanishingStatement` | no proof in the Library |
| `Global.CuspidalPairGlobalFunctionalEquationStatement` | no proof in the Library |
| `Global.CuspidalPairGlobalFunctionalEquationTCStatement` | no proof in the Library |
| `Global.CuspidalPairPoleTCStatement` | no proof in the Library |
| `CuspidalSigmaLiftConductorStatement` | no proof in the Library |
| `CuspidalSpectralRigidityStatement` | no proof in the Library |
| `CyclicPrimeIsobaricBaseChangeStatement` | no proof in the Library |
| `Henniart.CyclicPrimeStepHerbrandPsiStatement` | no proof in the Library |
| `CyclicRegularInductionStatement` | no proof in the Library |
| `CyclicRegularInductionTCStatement` | no proof in the Library |
| `CyclicRegularOrbitLiftStatement` | no proof in the Library |
| `CyclicRegularOrbitLiftTCStatement` | no proof in the Library |
| `CyclicStableDescentStatement` | no proof in the Library |
| `CyclicStableDescentTCStatement` | no proof in the Library |
| `CyclicWeakBaseChangeComplexPlaceStatement` | no proof in the Library |
| `CyclicWeakBaseChangeComplexPlaceTCStatement` | no proof in the Library |
| `CyclicWeakBaseChangeSupercuspidalStatement` | no proof in the Library |
| `CyclicWeakBaseChangeSupercuspidalTCStatement` | no proof in the Library |
| `DescentStepStatement` | no proof in the Library |
| `EqualArchimedeanFactorizationStatement` | no proof in the Library |
| `Correspondence.FullCorrespondenceRestrictionStatement` | no proof in the Library |
| `FundamentalLemmaStatement` | no proof in the Library |
| `GroupSchemeTwistedCuspidalSpectralExpansionStatement` | no proof in the Library |
| `Harris1998Theorem12CuspidalStatement` | no proof in the Library |
| `HarrisSupercuspidalLocalComparisonStatement` | no proof in the Library |
| `Global.PoleComparison.HenniartCompositeMapStatement` | no proof in the Library |
| `HenniartCompositeMapTCStatement` | no proof in the Library |
| `Global.HenniartGlobalizationExactStabilizerStatement` | no proof in the Library |
| `IsobaricHeckeComplexPlaceParameterStatement` | no proof in the Library |
| `KummerStageGaloisQuotientStatement` | no proof in the Library |
| `LaumonDeligneCountStatement` | no proof in the Library |
| `LaumonDeligneWeilCountStatement` | no proof in the Library |
| `LocalCyclicBaseChangeStatement` | no proof in the Library |
| `Henniart.NumericalBaseCaseStatement` | no proof in the Library |
| `NumericalDescentStatement` | no proof in the Library |
| `NumericalInjectionRefinedStrataStatement` | no proof in the Library |
| `NumericalOrbitCountStatement` | no proof in the Library |
| `Henniart.NumericalSurjectivityStatement` | no proof in the Library |
| `Conductor.OrderedUnramifiedCorankOneGenerationStatement` | no proof in the Library |
| `Conductor.OrderedUnramifiedWhittakerStatement` | no proof in the Library |
| `Proposition48AuxiliaryParityNormalizationStatement` | no proof in the Library |
| `Proposition48AuxiliaryParityUntwistStatement` | no proof in the Library |
| `Proposition48ExactStabilizerPrimeBranchStatement` | no proof in the Library |
| `Proposition48ExactStabilizerReductionStatement` | no proof in the Library |
| `Proposition48ExactStabilizerReductionTCStatement` | no proof in the Library |
| `Proposition48ExactStabilizerSingletonBranchStatement` | no proof in the Library |
| `Proposition48PrimeBranchStatement` | no proof in the Library |
| `Proposition48SingletonBranchStatement` | no proof in the Library |
| `Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement` | no proof in the Library |
| `PoleComparison.RelativeCertifiedPoleComparisonsTCStatement` | no proof in the Library |
| `Global.PoleComparison.RelativeIsometryFactorStatement` | no proof in the Library |
| `RelativeIsometryFactorTCStatement` | no proof in the Library |
| `RestrictedCyclicBaseChangeCompatibilityStatement` | no proof in the Library |
| `RestrictedCyclicWeakBaseChangeComplexPlaceStatement` | no proof in the Library |
| `SigmaLiftCharacterIdentityStatement` | no proof in the Library |
| `SigmaLiftInductionStatement` | no proof in the Library |
| `StratumApproximationStatement` | no proof in the Library |
| `Henniart.SupercuspidalBoundedLevelFinitenessStatement` | no proof in the Library |
| `SupercuspidalStratumUpperBoundStatement` | no proof in the Library |
| `Henniart.SurjectivityStepStatement` | no proof in the Library |
| `TowerBaseChangeHeckeComponentStatement` | no proof in the Library |
| `TowerBaseChangeHeckeComponentTCStatement` | no proof in the Library |
| `ClassFieldTheory.Global.RelativeWeilGroup.WeakEquivalenceRigidityStatement` | no proof in the Library |
| `WeilTameReductionStatement` | no proof in the Library |
| `WeilTruncatedConductorCountStatement` | no proof in the Library |

The following names in backquotes in the note end in `Statement` but are not declarations of the Library: they are module names, parts of module names, or names of statements that the Library does not contain: `Henniart.CandidateBaseChangeCompatibilityStatement`, `Henniart.CandidateCompatibleNumericalInjectionsReductionStatement`, `HarrisProposition48SingletonBranchStatement`, `HenniartGLUpperBoundStatement`, `HenniartLaumonDeligneStatement`, `HenniartNumericalBaseCaseStatement`, `HenniartNumericalDescentStatement`, `HenniartTwistSwanStatement`, `SemilocalEquationTCStatement`, `TCStatement`.
