# Global automorphic library and Henniart inputs: coverage and assumptions

This is the initial coverage ledger of the global automorphic program. Its tables were checked
against Library commit `545ccb3366b363dc0fe0a6d000b281a88d7c2407`.
The program has two required outputs: a general connected-reductive automorphic
library over number fields, and the global inputs of Henniart's 2000
local-correspondence construction. Neither track is complete.

The registered roadmap
[`henniart-global-automorphic-roadmap-2026-11-02`](<literature/Global roadmap- Henniart's local Langlands correspondence and a modern automorphic library (2 November 2026).md>),
SHA-256
`7be7def5b4039086928d7a9844c50fe5cea58513c24108191cef1ff239f4c8e3`,
determines the planned coverage below. Planned source
locators are reading targets from that roadmap, not assertions that this ledger's
authors have read every original or that the corresponding theorem is formalized.
The section on checked reuse separately identifies checked results in the Library. The original
tables and the nine rows of checked reuse below are a snapshot at that Library
commit. The later sections record later developments, each checked against the Library commit
it names. Where a statement named in this note is now proved in the Library, the note says so
and names the proof.

## How to read the status

“Public statement” means a proposition definition in the Library. It does not prove that
proposition. “Public proof” below means a theorem in the Library whose type is the exact target.
An interface located in the source without a check of its entry into the Library is
identified as such.

The checks used Lean 4.34.0 and mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The Lean files of the nine checked results below were compared with the files as they first
entered the Library. The associated-factor Markdown has a later correction (see below).

## One construction path

The algebraic-groups part of the Library (`Langlands/GroupScheme/`)
holds rational/Galois group structures, parabolics, Levis, unipotent groups,
relative roots, character/cocharacter lattices and the algebraic determinant of
the adjoint action on the unipotent Lie algebra. The present program constructs
adelic topologies, Haar moduli and quotient analysis on those actual objects.
An algebraic determinant still needs comparison with the analytic modulus.
Number-field work need not wait for general integral-model completion.

The common path is:

1. Actual reductive adelic quotients and compatible function spaces, then the
   cuspidal analysis of GH Chapter 9.
2. Topological meromorphic families and actual Eisenstein/intertwining
   constructions, following Bernstein–Lapid.
3. Lapid's wave-packet isometry and imaginary-axis results, then Delorme's
   surjectivity and the unitary spectral transform.
4. Proved GL_n specializations and comparison maps to the current
   `Langlands.Automorphic` realizations; those supply the analytic inputs of the
   Henniart application.

The comparisons must preserve actual functions, topology, actions, measures and
growth hypotheses. `RationalInvariantFunctions` uses rational left
invariance and the positive right action `R(g)f(x) = f(x*g)`;
`ContinuousRationalFunctions` has the induced compact-open topology. This
realization is not already the split-centre quotient
`[G] = A_G G(F) \ G(A_F)` of GH (2.20).
The finite smoothness, real smoothness at infinity, standard compact finiteness,
simultaneous enveloping-centre finiteness and finite-slice growth conditions in
the existing GL_n spaces must survive comparison.

In particular, `OperatorRealization`, `CuspidalOperatorRealization` and
`CuspidalSpectralPresentation` in namespace `Langlands.Automorphic` retain
genuine function spaces and actions. A supplied spectral or tensor presentation
does not prove its existence for every irreducible representation. Whole-operator
stable-core results do not by themselves give full archimedean translation
stability of compact-finite forms.

The current `Langlands.Automorphic.constantTerm` in
[`ConstantTerm.lean`](../../Langlands/Automorphic/ConstantTerm.lean) integrates
over maximal-block additive unipotent quotients, with explicit compactness of
`AdeleQuotient F`. Its comparison with all rational parabolics was an obligation at this
snapshot; the Library now proves `GeneralLinearParabolicCuspidalComparisonStatement`
(`generalLinearParabolicCuspidalComparison`), see the
[L1 note](l1-reductive-quotient-measure-coverage.md), §4. Compact additive `A_F/F`, or compact norm-one idele classes, does not
prove finite covolume of an adelic reductive quotient.

## Library track

The sources in this table are planned original-source obligations unless a
checked result below supplies a narrower result in the Library.

| Block | Required source correspondence | Current interface and proof boundary |
| --- | --- | --- |
| L1: quotients and spaces | GH (2.20), Chapters 2 and 9; applicable reduction theory and MW95 I–II | Construct actual `[G]`, quotient measures, Siegel sets, finite volume, smooth/finite-level/archimedean spaces, uniform moderate growth, constant terms and cusp forms. Existing additive quotient and GL_n function objects are reuse inputs; no general-reductive completion is credited here. |
| L1: cuspidal analysis | GH 9.1.2, 9.1.3 and §§9.2–9.5; 9.6.4, 9.6.5, 9.7.1, 9.7.3; MW95 I.2.12 for 9.7.1 | Closed cuspidal subspace, trace class, discrete decomposition with finite multiplicities, rapid decay and algebraic/Hilbert comparison remain required. The verified GL_n differential-growth proof is narrower: its growth constants can depend on derivative, form and finite slice. It does not establish uniform moderate growth or these spectral results. |
| L2: function-space meromorphy | BL §2.3, §§3.1–3.2 and Appendix A; MW95 I–II | Build the function-space topology and local common denominators, then actual Eisenstein and intertwining constructions. Pointwise scalar continuation is insufficient. |
| L2: continuation identities | BL Lemma 6.10 and Corollary 8.6; GH 10.2.3 and 10.3.2; source-qualified MW95 IV.1.8, IV.1.10 | Constant-term formulae, functional equations, cocycles/composition, root-hyperplane singularities and Fréchet continuation, with exact convergence and normalization hypotheses. Imaginary-axis holomorphy is a separate L3 result, not a conclusion assigned to BL alone. |
| L3: isometry and regularity | Lapid 2011 Proposition 2, Theorem 2, p.314, and Proposition 6, pp.329–330; its Working Hypothesis p.312 | Arthur truncation, Langlands' combinatorial lemma, `(G,M)`-families, Schwartz estimates and direct integrals must be constructed. Prove L² wave packets, the Weyl-compatible isometry with weight `\|P(M_P)\|⁻¹`, imaginary-axis holomorphy and source-qualified unitarity. |
| L3: completeness | Delorme 2023 Theorem 7.9, p.33; GH 10.5.1, (10.22)–(10.24) | Surjectivity requires BL/Lapid and explicit accounts of Lapid 2013, Bernstein Plancherel support and Franke temperedness. Inducing data range over the discrete spectrum, not only cuspidal data. The actual unitary transform remains required. |
| L4: inducing data and isobaric objects | GH 10.7.2, JS-II 4.4; GH 10.7.5–10.7.6 | The checked `CuspidalSpectralRigidityStatement` supplies mixed-rank trace independence and numerical recovery as unproved propositions (the Library now derives it from `CuspidalPairPoleStatement`, by `cuspidalSpectralRigidityLandauReduction` with the proved `cuspidalPairAbsoluteConvergence`). It supplies no general induced/isobaric realization bridge. Isobaric sums require the correct irreducible quotients; arbitrary automorphic subquotients of cuspidal induction are not all isobaric. |
| L4: Whittaker and multiplicity | GH 11.3.6, 11.4.3; GH's general-rank citation to Cogdell 2007 | Whittaker expansion and cuspidal multiplicity one remain required. The roadmap records Cogdell 2007 as missing; acquire and register it before relying on it. |
| L4: pair factors and global analysis | GH 11.5.2, 11.7.1; JPSS; Shahidi 1981 Theorem 4.1; Jacquet 2009 for archimedean theory | Local unitary regularity and global continuation, poles, functional equation and growth remain distinct obligations. The roadmap also records Barthel–Ramakrishnan 1994 as missing. No Ramanujan hypothesis is silently imposed. |
| L4: rigidity and pole detection | GH 11.7.2–11.7.3, JS-I 4.8; Shahidi 1981 Theorem 5.2, p.353; GH 11.8.1 | Strong multiplicity one retains almost-all-place equality. Partial pair L-function nonvanishing on `Re(s)=1` is a required global theorem; local GH 11.5.2 does not replace it. Pole counting needs omitted-factor holomorphy and nonvanishing. |

The optional MW89 GL_n residual-spectrum classification is separate.
Spectral completeness by itself neither classifies the discrete inducing data
nor constructs a trace formula.

The actual normalized idelic absolute value is already available in
`Langlands.Global.IdeleAbsoluteValue`; it is among the checked results below. In particular, `full_diagonalUnits` proves the normalized product
formula for actual principal ideles, and `ideleClass` descends the continuous
character to the actual principal quotient. Identification with Haar moduli,
parabolic determinant characters and relative norms remains separate. The
roadmap's observation that the formula is absent from the pinned mathlib must
not be read as a claim that no project construction exists.

## Henniart track

| Block | Source correspondence | Current declaration or construction boundary |
| --- | --- | --- |
| H1: finite-place comparison | Henniart 1986 Theorem 4.1 and §4.3; Henniart 2000 §§2.3–2.8 | The finite-exceptional-set engine must compare actual meromorphic factors using one finite set containing infinity and all bad places. Cancellation must be proved at every auxiliary place after highly ramified twists. Nonzero factors and factor/measure existence cannot be omitted. |
| H1: polynomial separation | Henniart 1986 Lemma 4.4, printed p.159/PDF16; reciprocal-radius criterion is derived content | `Langlands.Global.GammaSeparationStatement` in `Langlands.Global.Factors.SeparationStatement` is the conjunction of `GammaPolynomialSeparationStatement` and `ReflectedRootRegionStatement`. Its separate four-polynomial target is not the already proved two-polynomial reflection lemma. The Library proves it, as `gammaSeparation` (`Langlands/Global/Factors/SeparationProof.lean`). |
| H1: pairing and poles | Henniart 2000 §§2.5–2.8 and Appendix; Shahidi 1981 Theorem 5.2 | Preserve rank, unitarity/temperedness, finite support and degree/positivity conditions. Pairing/isometry and pole orders remain conditional on genuine analytic inputs until L4 discharges them. |
| H2: arithmetic and characters | Henniart 2000 §§3.3–3.7; Henniart 1984 Lemma 3.6; Artin–Tate X.2 Theorem 5; Harris 1998 Lemma 4.7 | The detailed source-to-target table below preserves the different field, character, stabilizer, tower and normalization obligations. The CM and general-position statements are in the Library. No H2 existence proof was in the Library at this snapshot; the Library now proves the field-realization, character-prescription, CM and general-position aggregates (see the H2 table below). |
| H3: global construction and factors | Henniart 2000 global construction and §§2.3–2.8; Henniart 2001 §§5.5–5.12 and §7.3 for the qualified variants | Assemble actual realizations, weak association, local maps and factor objects on individually stated deep hypotheses. The checked `Langlands.ClassFieldTheory.Global.RelativeWeilGroup.AssociatedFactorStatement` is a finite-place, relative-Weil, cuspidal statement family, not a proved complete global-to-local theorem. |
| H4: discharge | Arthur–Clozel III.3.1, III.4.2, III.5.1, III.6.2; HH95; Clozel/Clozel–Labesse/Kottwitz and the separate Harris/Shimura chain | Keep transfer and geometry as explicit sourced hypotheses in H3 until independently proved. Trace-formula and geometric Galois-existence work are long-term obligations, separate from the modern spectral-completeness theorem. |

### H2 source-to-target detail

The following rows were audited against the sources, within the direct-reading bounds given
after the table. Unqualified declaration names in this subsection have prefix
`Langlands.Global`. The five arithmetic statement modules compiled without diagnostics; the CM
and general-position statements were also checked against their entry into the Library (see
“Checked reuse” below). Compilation records declaration
availability, not the truth of these propositions. The last column gives the Library's proofs.

| Block and original passage | Current target declarations and scope | Construction and proof obligations | Proof in the Library |
| --- | --- | --- | --- |
| Totally-real realization: Henniart 2000 §3.3 p.449; Henniart 1984 Lemma 3.6 pp.34–35 | `TotallyRealGaloisRealizationStatement.{u,v}` in `Arithmetic.FieldRealizationStatement`: arbitrary-universe p-adic fields, totally-real number fields, full global/local Galois-group comparison, unique place, compatible continuous completion equivalences. `SplitAuxiliaryQuadraticsStatement.{u}`: real and imaginary quadratics split at p, with disjointness from the supplied totally-real field. Aggregate `FieldRealizationStatement`. | Actual weak approximation/Krasner realization and totally-real strengthening; actual split quadratic construction. These targets do not construct the later CM composita, intermediate-field tower or paired completion data. | All three are proved: `totallyRealGaloisRealization` (`Langlands/Global/Arithmetic/FieldRealizationProof.lean`), `splitAuxiliaryQuadratics` (`Langlands/Global/Arithmetic/SplitAuxiliaryQuadraticsProof.lean`) and the aggregate `fieldRealization` (`Langlands/Global/Arithmetic/FieldRealizationAggregateProof.lean`). |
| Finite-order prescription and twist isolation: Artin–Tate X.2 Theorem 5 p.80; Henniart 1986 Proposition 3.4/§4.3 | `FiniteOrderCharacterPrescriptionStatement.{u}`, `LocalCharactersArbitrarilyRamifiedStatement.{u}`, `RamifiedTwistIsolationStatement.{u}` in `Arithmetic.CharacterPrescriptionStatement`. Actual idele-class characters and completion units; unrestricted order bound **2n**, whole archimedean factor, arbitrary nontriviality on `1 + m^r`, disjoint selected/ramified sets, trivial infinity component for isolation. | Grunwald–Wang and local finite-order character/depth construction; assembly with a common finite order. No claim of order n without the Wang compatibility condition. H1 consumes isolation but does not thereby prove its arithmetic input. | All three are proved: `finiteOrderCharacterPrescription_proof` (`Langlands/Global/Arithmetic/CharacterPrescriptionProof.lean`), `localCharactersArbitrarilyRamified` (`Langlands/Global/Arithmetic/LocalCharactersArbitrarilyRamifiedProof.lean`) and `ramifiedTwistIsolation` (`Langlands/Global/Arithmetic/RamifiedTwistIsolationProof.lean`). |
| CM Lemma 1: Henniart 2000 §3.5 p.450 | `CMUnramifiedInfinityRealizationStatement.{u}` in `Arithmetic.CMCharacterStatement`: anticyclotomic integral infinity type, **one common positive scaling**, actual complex conjugation, conjugate self-duality and unramifiedness at every finite place. Current scope is any CM field, generalizing the source's chosen quadratic setup. | Class-group/unit/norm-quotient construction and finite-obstruction killing. No theorem is supplied by the statement publication. | Proved: `cmUnramifiedInfinityRealization` (`Langlands/Global/Arithmetic/CMUnramifiedInfinityProof.lean`). |
| CM Lemmas 2–3: Henniart 2000 §3.6 pp.450–451 | `CMFiniteCharacterPrescriptionStatement.{u}`, `IntegralUnitCharacterExtensionStatement.{u}`, `CMRegularUnitPrescriptionStatement.{u,v}`; aggregate `CMCharacterGlobalizationStatement`. Finite selected places are disjoint from their conjugates; full finite-order local prescription is the Lemma 2 target. The final regular Lemma 3 target prescribes **integral units only**, with distinct weights above an imaginary-quadratic embedding and the same positive scaling. | Extend integral-unit characters to finite-order local characters; prescribe at selected and conjugate places; form the conjugate quotient; combine with unramified infinity realization. Uniformizer values must remain free in the final target. Central-character and Harris-normalization conclusions still require explicit comparisons. | All proved: `cmFiniteCharacterPrescription` (`Langlands/Global/Arithmetic/CMFiniteCharacterPrescriptionProof.lean`), `integralUnitCharacterExtension` (`Langlands/Global/Arithmetic/IntegralUnitCharacterExtensionProof.lean`), `cmRegularUnitPrescription` (`Langlands/Global/Arithmetic/CMRegularUnitPrescriptionProof.lean`) and the aggregate `cmCharacterGlobalization` (`Langlands/Global/Arithmetic/CMCharacterGlobalizationProof.lean`). |
| Auxiliary norm stabilizer: Henniart 2000 §3.4(3); Harris 1998 proof of Lemma 4.7 pp.204–206, (4.12)–(4.13) | `HasExactUnitNormStabilizer`, `AuxiliaryCharacterStatement.{u,v}` in `Arithmetic.AuxiliaryCharacterStatement`. Actual determinant norm, Galois action, exact stabilizer **on valuation units**, arbitrary depth and all primes including 2. | Normal-basis logarithmic-lattice character construction, finite-order reduction, exactness and depth. Harris's literal embedding `(Z/2^N Z)ˣ → Cˣ` is unavailable for N ≥ 3. A sufficiently deep cyclic principal-unit construction is a proposed repair, not a proved replacement; `1+2Z₂` itself has torsion. | Proved: `auxiliaryCharacterFirstOrder` (`Langlands/Global/Arithmetic/AuxiliaryCharacterFirstOrderProof.lean`), for all primes including 2. |
| General position: Harris 1998 Definition 4.5 and Lemma 4.7 p.201, proof pp.204–206; Serre IV §2 pp.67–68 for solvable local Galois groups | `GeneralPositionOfExactStabilizerStatement.{uF}`, `ExactStabilizerCharacterStatement.{uF}`, `GeneralPositionCharacterStatement.{uF}`; aggregate `HarrisGeneralPositionStatement` in `Arithmetic.GeneralPositionStatement`. `GeneralPosition.IsInGeneralPosition` uses actual Weil subgroups, finite-index Mackey constituents and a cyclic-prime tower from the normal closure. | Separate unit-norm-to-Weil stabilizer transport and conductor/depth comparison, Clifford–Mackey irreducibility, and actual solvable-group/fixed-field tower. Existence of a normalized reciprocity family is a separate obligation: these targets quantify over a supplied normalized family. | The aggregate is proved: `harrisGeneralPosition` (`Langlands/Global/Arithmetic/HarrisGeneralPositionProof.lean`), by `auxiliaryGeneralPositionReduction` from `auxiliaryCharacterFirstOrder`. `generalPositionOfExactStabilizer` is proved separately; `ExactStabilizerCharacterStatement` follows from `AuxiliaryCharacterStatement` by `exactStabilizer_of_auxiliary`. |
| CM/tower and H3 adapter: Henniart 2000 §§3.3–3.4, 3.7; corrected Harris setup | Existing `Harris.PlaceDatum`, `Harris.PlaceDatum.IsCompatible`, `Harris.PlaceDatum.HasComponent`, `Harris.IsRelativelyRegular`, `Harris.IsAlgebraicAfterTwist`, `Harris.IsProposition48Datum` in `Arithmetic.HarrisSetup`. | Construct actual CM composita/towers and compatible places/completions, then compare local components and infinity types. CM regular integral weights alone do not produce Harris's full local prescription or `IsAlgebraicAfterTwist ([E':E]-1)`. Retain the half-norm parity correction when intermediate ranks change. | Definitions; no target. |
| Brauer/rank-one route: Henniart 2000 §3.7 and global functional equations | Consume existing virtual-representation, rank-one local-constant and arithmetic functional-equation objects; no parallel object family proposed here. | Actual Brauer/induction identities and factor adapters, preserving auxiliary local cancellation and central characters. The H2 rows above do not discharge these identities or deep transfer/geometry. | No target; this row names the identities still to be stated. |

The audit read Henniart 2000 pp.448–451 (PDF 10–13), including
§§3.1–3.8 and the printed Lemmas 1–3 proofs; Henniart 1984 Lemma 3.6
pp.34–35 (PDF 35–36); Artin–Tate X.2 pp.78–81 (PDF 87–90), including
Theorem 5's proof; Harris 1998 pp.204–206 (PDF 28–30) and its TeX proof
lines 1740–1824; and Serre IV §2 pp.67–68 (PDF 74–75). Other H2
locators are inherited from paired statement documentation unless they fall in
these ranges.

Registered sources are `henniart-2000-simple-proof`,
`henniart-1984-gl3`, `artin-tate-2009-class-field-theory`,
`harris-1998-local-langlands` and `serre-1979-local-fields`.
The total-reality strengthening is attributed to Henniart 2000 §3.3, rather
than asserted verbatim in Henniart 1984 Lemma 3.6. Harris's source-folder
`CORRECTION_SOURCE.md` describes corrections to Harris 1997 contained in the
1998 article; it does not establish an erratum to Harris 1998. The all-primes
auxiliary-character construction, including `p=2`, is proved: `AuxiliaryCharacterStatement` is
`auxiliaryCharacterFirstOrder` (`Langlands/Global/Arithmetic/AuxiliaryCharacterFirstOrderProof.lean`).

## Checked reuse

The commit given for each result is the Library commit at which it first appeared. Import the
declarations by module name. The files were compared against Library
`545ccb3366b363dc0fe0a6d000b281a88d7c2407`.

| Result and exact current interface | First appeared at Library commit | Scope retained |
| --- | --- | --- |
| `Langlands.Global.IdeleAbsoluteValue.full` and `ideleClass` in [`IdeleAbsoluteValue.lean`](../../Langlands/Global/IdeleAbsoluteValue.lean) | `00315d47b3cf847fb5aa4184c78df11887f7fe20` (construction) | Genuine normalized finite/infinite/full continuous idele characters, principal triviality `full_diagonalUnits`, quotient descent and local restrictions. This is a construction, not a proof of a stated target; no Haar-modulus, relative-norm or automorphic-existence comparison is supplied. |
| `Langlands.Global.CMCharacterGlobalizationStatement` in [`CMCharacterStatement.lean`](../../Langlands/Global/Arithmetic/CMCharacterStatement.lean) | `fe68653a42ed5ae0a2d7f5cef0697a68e8acc978` | Four propositions (unproved at this snapshot; all now proved, see the H2 table) generalizing Henniart 2000 Lemmas 1–3 to arbitrary CM fields and finite conjugate-separated sets, retaining common positive scaling and final integral-unit prescriptions. Auxiliary exact stabilizers and completion/Harris adapters remain separate. |
| `Langlands.Global.HarrisGeneralPositionStatement` in [`GeneralPositionStatement.lean`](../../Langlands/Global/Arithmetic/GeneralPositionStatement.lean) | `9a1bc5f8b8379aa4fe176f3af65ec4c9d96fc715` | Concrete Weil subgroups, Mackey constituents and normal-closure tower; supplied normalized reciprocity remains a hypothesis. Residue characteristic 2 is included in the statements, with the cited construction gap retained. No existence or implication-between-targets proof was supplied at this snapshot; the Library now proves the aggregate, as `harrisGeneralPosition`. |
| `Langlands.Automorphic.automorphicDifferentialGrowth` in [`DifferentialGrowthProof.lean`](../../Langlands/Automorphic/DifferentialGrowthProof.lean), proving `AutomorphicDifferentialGrowthStatement` | `8f53f05bb76983088fd64f190658c6ac4c3edc1b` | Genuine GL_n enveloping action, arbitrary number field and every natural rank, with bounds separately on finite slices. Does not prove general-reductive uniform moderate growth or spectral existence. |
| `Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement` in [`CuspidalSpectralRigidityStatement.lean`](../../Langlands/Automorphic/Unramified/CuspidalSpectralRigidityStatement.lean) | `0123ad79ddfe032cfbdceb25fbf4cf3dbf574612` | JS-II printed pp.805–809, Theorem 4.2 and numerical recovery in Theorem 4.4. Actual full cuspidal classes, supplied genuine presentations, mixed positive ranks, repetitions and one finite exception set. Analytic independence/recovery proofs, presentation existence/uniqueness and induced/isobaric realization remain open (the Library now derives the statement from `CuspidalPairPoleStatement`, by `cuspidalSpectralRigidityLandauReduction` with the proved `cuspidalPairAbsoluteConvergence`). |
| `Langlands.Automorphic.Unramified.CyclicCuspidalFiberStatement` in [`CyclicCuspidalFiberStatement.lean`](../../Langlands/Automorphic/Unramified/CyclicCuspidalFiberStatement.lean) | `9de4c69288df556276e9782428eda52c7ee37341` | AC89 III.3.1, printed pp.199–201: cyclic extension, same positive rank, actual norm-trivial finite-order twist, all places above and residue-degree powers. The common-upstairs consequence assumes the analytic proposition; no lifting/descent proof follows. |
| `Langlands.ClassFieldTheory.Global.RelativeWeilGroup.AssociatedFactorStatement` in [`AssociatedFactorStatement.lean`](../../Langlands/Automorphic/AssociatedFactorStatement.lean) | `efef3e8dad656737d40a56704c6373cf894d3cbd` | Henniart 2000 §§2.3–2.4, printed pp.444–445; Henniart 1986 Theorem 4.1, Lemma 4.4 and Proposition 4.5, pp.157–160. Four unproved propositions with the qualifications below. |
| Current [`AssociatedFactorStatement.md`](../../Langlands/Automorphic/AssociatedFactorStatement.md) correction | `bc8de2287e5c24972c55277b2aa9611523dfc5dc` (documentation correction) | Lean unchanged. The corrected prose acknowledges conditional existential claims for measures, common factors and inducing blocks; it does not claim witnesses were constructed or propositions proved. Current Lean matches the original; current Markdown matches this correction. |
| `Langlands.RankinSelberg.reflectionRigidity` in [`ReflectionRigidityProof.lean`](../../Langlands/Representation/RankinSelberg/ReflectionRigidityProof.lean), proving `ReflectionRigidityStatement` | `84f5d5a32df09643d499627f7ca72504805d3365` | Internal two-polynomial reciprocal-reflection rigidity with a strict radius gap, normalized polynomials, arbitrary integer monomial exponent and complex unit. Reuse with rational-evaluation infrastructure; it is not a proof of the four-polynomial GammaSeparation conjunction. |

The associated-factor conjunction comprises `AssociatedGammaStatement`,
`AssociatedTemperedFactorStatement`, `AssociatedSupercuspidalInductionStatement`
and `AssociatedCuspidalFactorStatement`, all in
`Langlands.ClassFieldTheory.Global.RelativeWeilGroup`. Its retained limits are:

- Finite-level relative Weil groups, not Henniart's absolute global Weil group.
- Actual cuspidal classes, not the full isobaric/noncuspidal source scope.
- Finite places; local maps and canonical additive-character components are
  explicitly quantified, with no existence conclusion for those maps.
- Supplied genuine spectral presentations, with explicit irreducibility and
  admissibility of each presented local factor; Flath existence is not supplied.
- Arithmetic class families and local-constant systems satisfying their stated
  axioms remain actual hypotheses.
- The matching predicates assert a self-dual measure exists and quantify over
  every such measure; L, dual L and epsilon matching require their own objects.
- Unitarity, central-character unitarity and temperedness occur at their actual
  distinct scopes; gamma equality alone does not supply the separation
  hypotheses.

These are disclosed scope differences of a partial statement,
not discharged construction or analytic obligations.

## Deep hypotheses and their discharge

| Input allowed explicitly in a conditional H3 theorem | Eventual discharge route and boundary |
| --- | --- |
| Actual global Rankin–Selberg functional equations, analytic regularity, inducing-data rigidity and boundary nonvanishing | L1–L4 through the shared general library and proved GL_n comparisons. These are obligations of the Library, not permanently outsourced deep assumptions for program completion. |
| Highly ramified stability and actual local factor/measure, local-map and presentation existence | H1/H2 and the existing local-factor, CFT and automorphic-definition files. The finite-S engine must name each missing input, rather than turn absent factor objects into vacuous implications. |
| AC89 III.3.1 twists | Checked public statement above; analytic proof still an explicit hypothesis. |
| AC89 III.4.2(a–f) lifting/descent, III.5.1 local base-change compatibility, III.6.2–4 automorphic induction | Existing statement scope; H4 trace-formula discharge remains open. Almost-all Hecke-eigenvalue induction does not imply ramified compatibility. |
| HH95 ramified functoriality | Separate sourced input where actually used; do not infer it from weak association or insert LLC-dependent compatibility into its own proof. |
| Weak geometric Galois existence, He2001 §5.5 | Clozel/Clozel–Labesse/Kottwitz, together with the Shimura-variety work. Retain `F = F⁺ I`, conjugate self-duality, regular algebraicity, and a discrete-series place split in `I`. Output is semisimple of dimension `a*n`, `a ≥ 1`, and the almost-everywhere shifted L identity has power `a`; no `a = 1` assumption. |
| Harris non-Galois induction and cohomology | Separate Harris/Shimura chain, following He2001 §§5.6–5.12, Taylor's corrections and the [current audit](../henniart/audit.md) and [Harris note](../henniart/harris-1999.md). The located `Langlands.Global.Harris.Proposition48Statement` is not credited here as a proof. |

Numerical surjectivity (Henniart 1988), epsilon characterization (1993),
extension to all representations and equal characteristic remain outside this
program's global-input conclusions. Henniart 2001's embedding-problem variant
is not an explicit description.

## Existing files and the program's three goals

Existing automorphic definitions are in `Langlands/Automorphic/` and `Langlands/Global/` (for
example `IdeleAbsoluteValue`). Existing global statements, including the outstanding transfer,
rigidity and associated-factor statements, are in `Langlands/Automorphic/` (for example
`AssociatedFactorStatement.lean` and `Unramified/`) and `Langlands/Global/Arithmetic/`. The
general extension adds proved comparisons rather than replacing these files. Algebraic structure
is in the algebraic-groups part of the Library (`Langlands/GroupScheme/`). Pairing and
finite-witness work builds on the existing virtual-lattice prerequisites.

| Goal | Public interface available at the snapshot | Missing program output |
| --- | --- | --- |
| Henniart's globalization | Current-source field, character and general-position proposition families named in H2; actual weak-induction relation `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.IsWeakAutomorphicInductionOf` in `Langlands.Automorphic.WeakAutomorphicInduction`. No proved complete globalization interface is identified by this ledger. | H2 constructions/proofs and H3 assembly on individually named transfer and geometry hypotheses, preserving exact local, infinity and central-character requirements. |
| Global-to-local factors | Checked public `AssociatedFactorStatement` and its four component targets; `GammaSeparationStatement` is now proved (`gammaSeparation`). The checked reflection theorem is a narrower reusable proof. | Proved H1 finite-S engine, separation and actual-factor adapters; L4 discharges global analytic hypotheses; H3 connects actual weak association and local components. |
| Harris's global input | Existing Harris/Shimura statements and audited sources are separate navigation inputs. No unconditional Harris theorem is credited here. | Independent cohomological/geometric construction and corrected conditional comparisons; not implied by either node above. |

The ledger itself supplies no mathematical completion evidence.

The ledger uses the registered roadmap and the detailed H2 source-to-target audit. Source
correspondence for the checked reused propositions and proofs follows their paired Markdown;
the wider tables remain explicit planning coverage.


## First continuation: analysis, H1 corrections, H2 and algebraic routing

This continuation was checked on 2 November 2026 against Library
`0ebc0efd383ff160084af3b33ab2b7806f7a1dde`. It preserves the original
snapshot above, including all nine rows of checked reuse.

### General analysis and source work

The following five modules, statements and source maps concern general analysis and the sources.

| Module, statement or source map | Exact scope and remaining boundary |
| --- | --- |
| Operator-ideal definitions | `Langlands.Analysis.OperatorIdeals`, a general analytic prerequisite. The definitions do not supply the operator-ideal theorems or automorphic applications. |
| Hilbert–Schmidt basis independence statement | `Langlands.Analysis.OperatorIdeals.HilbertSchmidtBasisIndependenceStatement`: rectangular bounded complex Hilbert operators, two independently indexed domain bases and four universe parameters; equivalent square summability and conditional equality of the squared sums. This is a disclosed derived extension of the separable endomorphism assertion in GH 9.1.1. The Library proves it, as `hilbertSchmidtBasisIndependence` (`Langlands/Analysis/HilbertSchmidtBasisProof.lean`). |
| GH Chapter 9 source map | `notes/automorphic/getz-hahn-cuspidal-source-map.md`. Original-source and errata reading, analytic dependencies and retained boundaries; no Lean theorem. |
| MW95 cuspidal-decay source map | `notes/automorphic/mw95-cuspidal-decay-source-map.md`. Records I.2.3, I.2.5, I.2.10–12 and I.2.17, including the central-growth and fixed-Siegel qualifications. It links to the GH source map. |
| Fixed-exponent differential growth statement | `Langlands.Global.ArchimedeanGL.FiniteUniformDifferentialGrowthStatement K n`: every natural rank, including zero, on the infinite-adelic GL_n group. For compact-finite, centre-finite smooth functions, each supplied growth bound with a nonnegative real constant and natural exponent is retained for every genuine enveloping derivative, allowing a new constant. This strengthens the derivative-dependent result; it does not prove the general adelic uniform-growth or cuspidal-decay obligations. The Library proves it, as `Langlands.Global.ArchimedeanGL.finiteUniformDifferentialGrowth` (`Langlands/Global/ArchimedeanFiniteUniformGrowthProof.lean`). |

The proofs of the two statements, `Langlands.Analysis.HilbertSchmidtBasisProof` and
`Langlands.Global.ArchimedeanFiniteUniformGrowthProof`, compiled with zero errors or
warnings and only `propext`, `Classical.choice` and `Quot.sound` reported.

### H1 corrections and retained analytic inputs

An impossible-input defect was found in the former
Hecke-twist and relative-gamma statements: `CommonTwistEulerInputs` fixed the
partial Euler tails for each character before the common exceptional set `B`
was chosen for two characters. Even the trivial-character GL_1/Q tail cannot
represent all products outside varying enlarged sets `B`. Those statements were withdrawn.

The correction keeps the local factor system fixed by the character while
indexing partial tails and their analytic data by both the character and `B`.
This repairs the indexing obligation without assuming the global functional
equations, ramified cancellation or factor certificates proved. The corrected and new
targets, with prefix `Langlands.Global`, are all proved in the Library:

| Target, with prefix `Langlands.Global` | Proof in the Library |
| --- | --- |
| `FunctionalEquationComparison.HeckeTwistComparisonStatement` | `heckeTwistComparison` (`Langlands/Global/Factors/HeckeTwistComparisonProof.lean`) |
| `FunctionalEquationComparison.RelativeGammaComparisonStatement` | `relativeGammaComparison` (`Langlands/Global/Factors/RelativeGammaComparisonProof.lean`) |
| `FactorSeparation.CertifiedFactorSeparationStatement` | `certifiedFactorSeparation` (`Langlands/Global/Factors/CertifiedFactorSeparationProof.lean`) |

The generic finite/germ comparison statements and the pole, pairing, Appendix and separation
proofs of H1 are treated in the later sections. No unconditional `AssociatedFactorStatement`
proof is claimed; this note records none.

### H2 statements and proofs

| Statement or proof and exact declaration, with prefix `Langlands.Global` | Scope | Proof in the Library |
| --- | --- | --- |
| Paired-place realization, `HarrisPairedPlaceRealizationStatement` | CM composita and two compatible place pairs are a statement target. Full intermediate towers, characters and Harris assembly are separate. | `harrisPairedPlaceRealization` (`Langlands/Global/Arithmetic/HarrisPairedPlaceRealizationProof.lean`) |
| Conditional assembly, `CMRegularUnitPrescriptionOfInputsStatement` | Three explicit existence inputs imply regular integral-unit prescription. The target does not discharge any of these inputs. | `cmRegularUnitPrescriptionOfInputs` (`Langlands/Global/Arithmetic/CMCharacterAssemblyProof.lean`) |
| Integral-unit extension proof, `integralUnitCharacterExtension` of `IntegralUnitCharacterExtensionStatement` | Extension of integral-unit characters to finite-order local characters. | `integralUnitCharacterExtension` (`Langlands/Global/Arithmetic/IntegralUnitCharacterExtensionProof.lean`) |
| Finite-prescription reduction, `CMFiniteCharacterPrescriptionOfFiniteOrderStatement` | Exactly `FiniteOrderCharacterPrescriptionStatement → CMFiniteCharacterPrescriptionStatement`. It isolates a reduction, not a construction of its finite-order premise. | `cmFiniteCharacterPrescriptionOfFiniteOrder` (`Langlands/Global/Arithmetic/CMFiniteCharacterPrescriptionReductionProof.lean`) |

Five further targets were set as separate proof obligations; all are proved in the Library (see
the H2 table above):

| Target | Boundary |
| --- | --- |
| `SplitAuxiliaryQuadraticsStatement` | Actual split auxiliary quadratics. |
| `TotallyRealGaloisRealizationStatement` | Actual totally-real realization and completion/Galois comparisons. |
| `IntegralUnitCharacterExtensionStatement` | The proof above. |
| `FiniteOrderCharacterPrescriptionStatement` | Retains the order bound 2n and the whole infinity component. |
| `CMUnramifiedInfinityRealizationStatement` | Retains one common positive scaling and unramifiedness at every finite place. |

At this continuation the auxiliary exact-stabilizer construction, its all-primes depth argument,
unit-norm-to-Weil transport, the solvable tower and the full Harris adapters
remained required as described in the H2 table, and these
reductions did not remove the residue-characteristic-2 issue or
the half-norm parity and central-character comparisons. The Library now proves the auxiliary
character statement for all primes and the general-position aggregate (see the H2 table).

### Algebraic routing and quotient conventions

The structural routing was checked against the
Library names for actual corepresented coefficient points, GL_n points,
`Dynamic.semidirectEquiv`, relative roots, lattices and adjoint constructions.
Standard parabolics and rational characters with split components
are algebraic prerequisites.
The algebraic determinant of `Ad` on `Lie U` and general structure proofs belong
to the algebraic-groups part of the Library; adelic moduli and their comparisons belong to L1.

For the GH quotient convention, `A_G` is the identity component of real points
of the greatest Q-split torus in `Res_{F/Q} Z_G`. It must not silently become
the greatest F-split central torus. At rank zero, the scalar map from `G_m` to
`GL_0` is not a closed immersion: an actual split-central construction must use
the trivial torus there or state a positive-rank restriction. L1 keeps the distinct
strict MW95 and weak GH Siegel domains and constructs the quotient/measure data
without storing the desired analytic conclusions as input fields.

Neither track of the program is complete.


## Operator traces: first results

This section was checked on 2 November 2026 against Library
`9d1720cbedcfd184cf48bf36249fc3029583cafa`. It does not update the H1/H2 status tables or
assert completion of any L1 analytic theorem.

| Exact public interface | First appeared at Library commit | Scope |
| --- | --- | --- |
| `Langlands.Analysis.OperatorIdeals.traceNormBasisIndependence` in [TraceNormBasisProof.lean](../../Langlands/Analysis/TraceNormBasisProof.lean), proving `TraceNormBasisIndependenceStatement` | `1271a6b7c9a470deaa1b8e2aadc2e2defd10f5b5` | The existing existential trace-class predicate is equivalent to summability of the positive real left-modulus diagonal in every supplied Hilbert basis, and the resulting `traceNormIn` sums agree when summable. Three independent universe parameters; no separability assumption. This result does not concern the full complex diagonal of A. |
| `Langlands.Analysis.OperatorIdeals.leftModulusFactorization` in [LeftModulusFactorizationProof.lean](../../Langlands/Analysis/LeftModulusFactorizationProof.lean), proving `LeftModulusFactorizationStatement` | `5d3754ec863f6d5013aca65cbcec0801e6972d1f` | For every bounded complex-linear endomorphism A of an arbitrary complete complex inner-product space, there is U with norm at most one and `A = (leftModulus A).comp U`. The proof uses continuous extension from a range closure, orthogonal projection and adjoints. It asserts no partial-isometry property. |
| `Langlands.Analysis.OperatorIdeals.HilbertSchmidtProductTraceStatement` in [HilbertSchmidtProductTraceStatement.lean](../../Langlands/Analysis/HilbertSchmidtProductTraceStatement.lean) | `9d1720cbedcfd184cf48bf36249fc3029583cafa` | A proposition target. For rectangular Hilbert–Schmidt maps B:E→F and C:F→E, it asserts absolute summability of the complex diagonals of CB and BC and equality of their specified-basis `traceIn` sums. The spaces and basis index types have four independent universes. It does not assert trace-class membership of either product. It is proved in the next section. |

The target, proof where applicable, and transitive project-import Lean/Markdown pairs of these
three declarations match the named Library commit.

These are general operator-theoretic prerequisites motivated by Getz–Hahn,
Definition 9.1.1 and the trace discussion on printed pp.240–241, and Exercises
9.1–9.2 on p.267. Their paired Markdown records the direct original-source
reading, complete October 2026 errata check and internal derivation boundaries.
The arbitrary-index and rectangular extensions, and the contractive
factorization, are internal results; they are not attributed verbatim to those
source passages. Parseval, the actual positive left modulus and
Hilbert–Schmidt basis independence give the implemented routes.

Trace-class factorization, absolute complex diagonals and their basis
independence for trace-class operators, canonical trace construction,
trace-class ideal laws and trace-class membership of Hilbert–Schmidt products
are distinct obligations; the next section records the proofs of several of them. Actual
automorphic convolution trace class,
closedness of the cuspidal space, rapid decay, algebraic/Hilbert comparison and
the general-reductive spectral decomposition are further obligations. These operator
results alone establish none of those conclusions.


## Operator traces: proofs

This section was checked on 3 November 2026 against Library
`ca102a8a50473f5a0f03f7fcd16cd21d996a6f7d`. It concerns only the operator modules named here.

| Exact interface, with prefix `Langlands.Analysis.OperatorIdeals` | Status in the Library | Scope and remaining work |
| --- | --- | --- |
| `hilbertSchmidtProductTrace` in [HilbertSchmidtProductTraceProof.lean](../../Langlands/Analysis/HilbertSchmidtProductTraceProof.lean), proving `HilbertSchmidtProductTraceStatement` | Proved; first appeared at Library commit `405ff58c5df69766419c9941161444531c1979ae`. | Rectangular Hilbert–Schmidt maps have absolutely summable complex diagonals for both compositions and equal specified-basis sums. The spaces and basis indices have four independent universes. This theorem alone does not assert trace-class membership of the compositions. |
| `traceClassFactorization` in [TraceClassFactorizationProof.lean](../../Langlands/Analysis/TraceClassFactorizationProof.lean), proving `TraceClassFactorizationStatement` | Proved; first appeared at Library commit `6e277941a7bd32cdcf50123da3df2754259d6be7`. | Every actual trace-class endomorphism A of an arbitrary complete complex inner-product space factors as `A = B.comp C` with both factors Hilbert–Schmidt on that space. The positive square root of the left modulus, its contractive factorization and bounded precomposition give the implemented proof. |
| `TraceBasisIndependenceStatement` in [TraceBasisStatement.lean](../../Langlands/Analysis/TraceBasisStatement.lean) | Statement first appeared at Library commit `405ff58c5df69766419c9941161444531c1979ae`. The Library proves it, as `traceBasisIndependence` ([TraceBasisProof.lean](../../Langlands/Analysis/TraceBasisProof.lean)). | The target asserts absolute complex-diagonal summability and equal `traceIn` sums in any two supplied Hilbert bases, with three independent universes. The proof compares both sums to one reversed Hilbert–Schmidt product. |
| `HilbertSchmidtProductTraceClassStatement` in [HilbertSchmidtProductTraceClassStatement.lean](../../Langlands/Analysis/HilbertSchmidtProductTraceClassStatement.lean) | Statement first appeared at Library commit `405ff58c5df69766419c9941161444531c1979ae`. Proved by `hilbertSchmidtProductTraceClass` in [HilbertSchmidtProductTraceClassProof.lean](../../Langlands/Analysis/HilbertSchmidtProductTraceClassProof.lean), first appeared at `a89596feabc7e1db11dbefead1032c9cfc0d1409`. | For arbitrary rectangular Hilbert–Schmidt B:E→F and C:F→E, the actual composition `C.comp B` is trace class. Two independent space universes. The proof constructs a factorization of the left modulus through the composition, then applies absolute product-diagonal summability. |
| `TraceClassIdealStatement` in [TraceClassIdealStatement.lean](../../Langlands/Analysis/TraceClassIdealStatement.lean) | Statement first appeared at Library commit `6820dc99b5972ed5761be21b4ac8afeba7584644`. The Library proves it, as `traceClassIdeal` ([TraceClassIdealProof.lean](../../Langlands/Analysis/TraceClassIdealProof.lean)). | Zero, addition, complex scalar multiplication, adjoint equivalence and bounded rectangular sandwich laws for the actual trace-class predicate, in two independent universes. Addition factors through the actual Hilbert direct sum `WithLp 2 (E × E)`. This statement supplies no proved trace-norm bound or trace linearity. |

The three proof pairs and three statement pairs above that were in the Library at the named
commit byte-match it.

A compilation of five trace proof modules, including the product-diagonal module, had zero
errors and warnings. Declaration inspection of the trace-basis proof confirmed the three
independent universe parameters and only standard axioms; that of the ideal-law proof
confirmed u/v and standard axioms with zero errors/warnings.

Source conventions remain Getz–Hahn, Definition 9.1.1 and the trace discussion,
printed pp.240–241, and Exercises 9.1–9.2, p.267, with the complete October 2026
errata checked. The source assumes separability. Arbitrary basis indices,
rectangular spaces, the Hilbert–Schmidt factorization of trace-class maps and
the ideal-law collection are documented internal extensions. The positive
left modulus is sqrt(A A*); the complex diagonal uses Mathlib's inner product
linear in its second variable. The public proof Markdown explains the
implemented arguments and does not attribute these exact broader quantifiers
to the original source.

Canonical trace construction and linearity are separate modules; this section records no proof
of them. Actual automorphic convolution trace class, cuspidal closedness, rapid decay,
algebraic/Hilbert comparison and the general-reductive spectral decomposition
are L1 obligations. No operator result in this section
establishes those conclusions or changes the conditional H3/H4 boundaries.


## First-order auxiliary character

This H2 section was checked on 3 November 2026 against Library
`622054b9c6b9f07feb1335165348ac66b27b39e5`. It concerns only the modules named here.

The five targets in the next table are focused internal prerequisites of the first-order
route, rather than theorems attributed verbatim to Harris or Henniart. The first
three first appeared in the Library at commit `25b91125ea94e88d741b206d633e82eb0d87c3e5`; the
last two at `071b82c1a715daffe0334ad25311484eaba312b0`. All five are now proved.

| Exact public target | Scope | Proof in the Library |
| --- | --- | --- |
| `Langlands.HarmonicAnalysis.PadicFiniteCoefficientSeparationStatement.{u}` in [PadicFiniteCoefficientSeparationStatement.lean](../../Langlands/HarmonicAnalysis/PadicFiniteCoefficientSeparationStatement.lean) | One inverse-prime-power threshold detects every nonzero coefficient in a finite set on the actual additive integer lattice. | `padicFiniteCoefficientSeparation` (`Langlands/HarmonicAnalysis/PadicFiniteCoefficientSeparationProof.lean`) |
| `Langlands.LocalClassField.QuadraticNormTraceStatement.{u,v}` in [QuadraticNormTraceStatement.lean](../../Langlands/ClassFieldTheory/Local/QuadraticNormTraceStatement.lean) | For every integral a and y in a finite compatible extension, the actual norm is `1+a*Tr(y)+a^2*r` with integral r. Every prime, independent universe and finite degree is retained. | `quadraticNormTrace` (`Langlands/ClassFieldTheory/Local/QuadraticNormTraceProof.lean`) |
| `Langlands.HarmonicAnalysis.PadicDeepUnitCharacterStatement.{u}` in [PadicDeepUnitCharacterStatement.lean](../../Langlands/HarmonicAnalysis/PadicDeepUnitCharacterStatement.lean) | The explicit conductor bound kills the multiplication error in the prescribed character `u ↦ psi(c*(u-1))` on actual principal units, with a uniform p-power annihilator. Character extension, nontriviality and stabilizers are separate. | `padicDeepUnitCharacter` (`Langlands/HarmonicAnalysis/PadicDeepUnitCharacterProof.lean`) |
| `Langlands.HarmonicAnalysis.PadicPrincipalUnitCharacterExtensionStatement.{u}` in [PadicPrincipalUnitCharacterExtensionStatement.lean](../../Langlands/HarmonicAnalysis/PadicPrincipalUnitCharacterExtensionStatement.lean) | Every continuous complex character of actual principalUnits n extends to finite positive order on field units, with value one at the supplied uniformizer. All supplied compatible topologies, p=2 and n=0 are retained. | `padicPrincipalUnitCharacterExtension` (`Langlands/HarmonicAnalysis/PadicPrincipalUnitCharacterExtensionProof.lean`) |
| `Langlands.HarmonicAnalysis.PadicDeepUnitNormTraceStatement.{u,v}` in [PadicDeepUnitNormTraceStatement.lean](../../Langlands/HarmonicAnalysis/PadicDeepUnitNormTraceStatement.lean) | Under the prescribed character formula and three valuation bounds it constructs the actual unit z=1+i(a)y, puts its norm in principalUnits n and computes `chi(Nz)=Circle.toUnits(psi(c*a*Tr(y)))`. Its proof uses the quadratic norm–trace result. | `padicDeepUnitNormTrace` (`Langlands/HarmonicAnalysis/PadicDeepUnitNormTraceProof.lean`) |

The algebraic `Langlands.Global.PrimitiveTraceStabilizerStatement` is a further
prerequisite; its proof is described in the next section.

### Complete private assembly and independent proof boundaries

The unchanged public targets are
[AuxiliaryCharacterStatement.lean](../../Langlands/Global/Arithmetic/AuxiliaryCharacterStatement.lean)
and [GeneralPositionStatement.lean](../../Langlands/Global/Arithmetic/GeneralPositionStatement.lean).
Their original-source correspondence remains Henniart 2000 §3.4 condition 3,
p.449, and §3.6 Lemma 3, p.451; Harris 1998 Definition 4.5 and Lemma 4.7,
p.201, with (4.12)–(4.13), pp.204–205. This section reuses their
source correspondence and leaves both target pairs unchanged. The first-order
implementation below is an internal alternative route. It is not attributed
to the literal source argument using an embedding of `(Z/2^N Z)^x`.

The implementation
`Langlands.Global.auxiliaryCharacterFirstOrder.{u,v}` has the declared
`AuxiliaryCharacterStatement.{u,v}` type and uses only
propext, Classical.choice and Quot.sound. It uses the six prerequisite results above. It
constructs finite
order, strict arbitrary-depth nontriviality and the actual exact norm stabilizer
for every prime, including two, every compatible finite Galois overfield and
every intermediate field. It is in the Library, in
`Langlands/Global/Arithmetic/AuxiliaryCharacterFirstOrderProof.lean`.

Besides the main proof, it uses integral
detection/trace helpers, topology comparison, the first-order family,
norm coordinates, the conditional exact stabilizer and depth helpers, and the six
prerequisite results above.

The implemented parameter choice is one common offset C and
`c=p^(C-2k)`, principal level `k*e`, with the quadratic error uniformly within
the additive conductor. Total-trace coordinates have value
`psi_F(p^(C-k)*Tr(b*y))`. Simultaneous integral linear detection separates every
unwanted automorphism. A separate nonzero weighted trace supplies nontriviality,
including the case L=F. Taking `k=C+N1+N2+r+1` gives the strict depth bound.
Module-topology uniqueness and actual inclusion isometry identify the supplied
intermediate topology and norm with the exact subtype data in the target.
Fixing automorphisms preserve the actual L norm, and every unwanted one is
detected on a norm-one coordinate unit. The implementation uses no p-adic
logarithm/exponential or division by two.

The Library's `Langlands.Global.auxiliaryGeneralPositionReduction` proves
`AuxiliaryCharacterStatement.{u,u} → HarrisGeneralPositionStatement.{u}`.
It is a conditional reduction, rather than an auxiliary existence proof.
`Langlands.Global.harrisGeneralPosition.{u}` applies that reduction to the
first-order construction (universe u, standard axioms); it is in the Library, in
`Langlands/Global/Arithmetic/HarrisGeneralPositionProof.lean`.

This composition retains the explicit normalized-reciprocity hypothesis of the
last two Harris conjuncts. It constructs no reciprocity family and supplies no
proof of `NormalizedSystemExistence` (`Langlands/ClassFieldTheory/Local/ReciprocitySystem.lean`;
this note records no proof of it). The local construction does not supply
prescribed global Hecke characters, paired field
towers, weak automorphic induction or H2 completion.

## Trace-stabilizer proof

This section was checked on 4 November 2026 against Library
`9caf47cacd8f25d9a56aa0737b4256267bf62d16`. The Library proves
`Langlands.Global.PrimitiveTraceStabilizerStatement`, as
`Langlands.Global.primitiveTraceStabilizer.{u,v}` in
[PrimitiveTraceStabilizerProof.lean](../../Langlands/Global/Arithmetic/PrimitiveTraceStabilizerProof.lean),
with its [paired proof explanation](../../Langlands/Global/Arithmetic/PrimitiveTraceStabilizerProof.md).
The proof first appeared at Library commit `476a152fd90d846bcb20b9897f53829a768b822c`; its build
and target check passed with the statement unchanged.

For any finite separable extension M/F and actual intermediate field L, the
theorem produces a nonzero primitive coefficient a in L such that preserving
`x ↦ Tr_M/F(a*x)` by precomposition is equivalent to pointwise fixation of L.
It retains independent field universes, arbitrary characteristic and no
normality hypothesis. The implemented proof combines trace invariance and
nondegeneracy with primitive-element generation and the actual inclusion of L.
It proves the algebraic prerequisite; multiplicative character existence,
continuity, finite order, norm compatibility and arbitrary depth remain
separate conclusions of the auxiliary construction.

The other prerequisites of the auxiliary construction are finite coefficient separation, the
integral quadratic norm–trace error, the prescribed deep-unit character, the normalized
principal-unit extension and the norm–trace character comparison; their proofs are described
in the following sections. The explicit normalized-reciprocity premise and the global
field/tower and Hecke-character obligations remain.

## Finite-separation proof

This section was checked on 5 November 2026 against Library
`a9f12d1e4a0823c676b8a7b9292f17ea7c1d08ee`. The theorem
`Langlands.HarmonicAnalysis.padicFiniteCoefficientSeparation.{u}` in
[PadicFiniteCoefficientSeparationProof.lean](../../Langlands/HarmonicAnalysis/PadicFiniteCoefficientSeparationProof.lean)
proves the unchanged proposition
`Langlands.HarmonicAnalysis.PadicFiniteCoefficientSeparationStatement.{u}`;
the [paired explanation](../../Langlands/HarmonicAnalysis/PadicFiniteCoefficientSeparationProof.md)
describes the implemented proof. It first appeared at Library commit
`409542525904dd50036abafdafb8ad1459eadade`; its build and target check passed with the
statement unchanged.

The proof chooses a finite maximum of coefficient-order bounds. For every
later exponent, the published lattice-annihilator implication and positive
integer order of the actual prime exclude triviality for each nonzero
coefficient; a zero coefficient gives triviality directly. The exact target
retains every prime including two, arbitrary carrier universe, supplied
compatible topology, every integer lattice level and empty coefficient sets.
This is an internal additive separation result. It constructs no multiplicative
auxiliary character or norm stabilizer.

The explicit normalized-reciprocity premise and the
global field/tower, Hecke-character, H2 and general automorphic obligations
remain.

## Quadratic, deep-unit and principal-unit proofs

This section was checked on 5 November 2026 against Library
`ee0c0dd6da0a631f199c2bc0aa6040eece98f41d`. Three more prerequisite proofs of the auxiliary
construction are in the Library. All three first appeared at commit
`0d12b7d171600d15516e52ee508d3aaca3e9cf9e`; for each, the build and target check passed with the
statement unchanged.

| Prerequisite and theorem |
| --- |
| Integral quadratic norm–trace error, `Langlands.LocalClassField.quadraticNormTrace.{u,v}` in [QuadraticNormTraceProof.lean](../../Langlands/ClassFieldTheory/Local/QuadraticNormTraceProof.lean) ([explanation](../../Langlands/ClassFieldTheory/Local/QuadraticNormTraceProof.md)) |
| Prescribed deep-unit character, `Langlands.HarmonicAnalysis.padicDeepUnitCharacter.{u}` in [PadicDeepUnitCharacterProof.lean](../../Langlands/HarmonicAnalysis/PadicDeepUnitCharacterProof.lean) ([explanation](../../Langlands/HarmonicAnalysis/PadicDeepUnitCharacterProof.md)) |
| Normalized principal-unit extension, `Langlands.HarmonicAnalysis.padicPrincipalUnitCharacterExtension.{u}` in [PadicPrincipalUnitCharacterExtensionProof.lean](../../Langlands/HarmonicAnalysis/PadicPrincipalUnitCharacterExtensionProof.lean) ([explanation](../../Langlands/HarmonicAnalysis/PadicPrincipalUnitCharacterExtensionProof.md)) |

The quadratic theorem gives, for every finite compatible extension E/F of
supplied p-adic fields and integral a and y, an integral r with
`N_E/F(1 + i(a)*y) = 1 + a*Tr_E/F(y) + a^2*r`, where i is the algebra map. It uses the published relative
integer structure and Mathlib's norm/trace localization. The deep-unit
theorem makes `u ↦ psi(c*(u-1))` a continuous character on the actual
principal units of level n under the stated valuation bound, killed by a
uniform p-power. The extension theorem extends every continuous character of
those principal units to a continuous finite-order character of the field
units, with value one at the supplied uniformizer. It uses the compact
normalized-norm-one units and the public finite-quotient character extension.
All three keep every prime including two and level zero. None of them
constructs nontriviality, depth or a norm stabilizer.

With these, five of the six prerequisites of the auxiliary construction are proved: trace
stabilizer, finite coefficient separation, quadratic norm–trace error, deep-unit character and
principal-unit extension. The sixth, the norm–trace character comparison, is proved in the
next section. The explicit normalized-reciprocity
premise and the global field/tower, Hecke-character, H2 and general automorphic
obligations remain.

## Norm–trace character and auxiliary-character proofs

This section was checked on 5 November 2026 against Library
`570fefbe5133b1afff1a5914f8de20920d97fda0`. The last prerequisite proof of
the auxiliary construction and the auxiliary assembly itself are in the Library. The norm–trace
character comparison first appeared at commit `0bd5bf67c3464359bc8da3b3100163d6ee3da352` and the
auxiliary assembly at `910675f18ad6c3d8b09c12c678a0243795a673b9`. For each, the build and target
check passed with the statement unchanged.

| Theorem |
| --- |
| Norm–trace character comparison, `Langlands.HarmonicAnalysis.padicDeepUnitNormTrace.{u,v}` in [PadicDeepUnitNormTraceProof.lean](../../Langlands/HarmonicAnalysis/PadicDeepUnitNormTraceProof.lean) ([explanation](../../Langlands/HarmonicAnalysis/PadicDeepUnitNormTraceProof.md)) |
| Auxiliary characters with the exact unit-norm stabilizer, `Langlands.Global.auxiliaryCharacterFirstOrder.{u,v}` in [AuxiliaryCharacterFirstOrderProof.lean](../../Langlands/Global/Arithmetic/AuxiliaryCharacterFirstOrderProof.lean) ([explanation](../../Langlands/Global/Arithmetic/AuxiliaryCharacterFirstOrderProof.md)) |

The norm–trace theorem proves the unchanged
`Langlands.HarmonicAnalysis.PadicDeepUnitNormTraceStatement.{u,v}`. Take a finite
compatible extension E/F of supplied p-adic fields in independent universes,
with supplied topological data on each, a continuous nontrivial additive
unitary character psi of F, a scalar c, a level n
and a continuous character chi of the units of F that agrees with
`psi(c*(u-1))` on the actual level-n principal units. Let a be an integer of F whose discrete valuation v satisfies
`v(a) < 1`, `v(a) ≤ exp(-n)` and `v(c)*v(a)^2 ≤ exp(conductor of psi)`.
Then for every integer y of E, the field unit `z = 1 + i(a)*y` has actual
determinant norm in the level-n principal units, and
`chi(N_E/F(z)) = psi(c*a*Tr_E/F(y))`. No finite-order premise on chi is used.

The auxiliary theorem proves the unchanged
`Langlands.Global.AuxiliaryCharacterStatement.{u,v}` for every prime, including
two. Take finite p-adic fields F and M in independent universes with M/F a
compatible finite Galois extension, an actual intermediate field L and a natural
number r. The theorem gives one continuous character chi of the units of L with a
positive finite annihilating exponent, a unit x of L with `‖x-1‖ < p^(-r)` in
the canonical norm of M and `chi(x) ≠ 1`, and the exact predicate
`HasExactUnitNormStabilizer L chi.toMonoidHom`. Under
this predicate, an F-automorphism of M fixes chi composed with the actual norm
to L on all valuation units of M exactly when it fixes L pointwise. The implemented
route uses first-order principal-unit coordinates, the integral quadratic norm
error and integral trace detectors. It uses no logarithm or exponential, no
odd-prime restriction and no reciprocity premise. The proof's Markdown
documents how this route differs from Harris's logarithmic argument.

With all six prerequisite proofs and the auxiliary assembly in the Library, the Harris
general-position composition `harrisGeneralPosition` applies `auxiliaryGeneralPositionReduction`
to `auxiliaryCharacterFirstOrder`; it is in the Library
(`Langlands/Global/Arithmetic/HarrisGeneralPositionProof.lean`, see the next section). The
composition keeps the explicit normalized-reciprocity premise and constructs no
reciprocity family. The global field/tower, Hecke-character, H2 and general
automorphic obligations remain.

## Harris general position and the H2 compositions

This section was checked on 5 November 2026 against Library
`ffddfca241fd480a4fb3b8c9215b48c488d7f97b`, with the file hashes rechecked
against Library commits `73016647c403b942bebe18fad4e569a83c342b52` and
`9d2c31eb3021c9de866cc7f8313284404b3f5ccc`. The
Harris composition and six H2 aggregate compositions are in the Library. For each, the build and
target check passed with the statement unchanged. All fourteen proof files have the same hash
in all three Library commits. The four
target statement pairs (`CharacterPrescriptionStatement`,
`CMCharacterStatement`, `FieldRealizationStatement` and
`GeneralPositionStatement`) are the same in all three Library commits. Every composition applies
published component theorems only; none adds a definition, hypothesis or axiom.

| Theorem | First appeared at Library commit |
| --- | --- |
| Full local Harris general position, `Langlands.Global.harrisGeneralPosition.{u}` in [HarrisGeneralPositionProof.lean](../../Langlands/Global/Arithmetic/HarrisGeneralPositionProof.lean) ([explanation](../../Langlands/Global/Arithmetic/HarrisGeneralPositionProof.md)) | `bc859155612cc8ca34e8e25175ce2f7775c217dc` |
| Ramified twist isolation, `Langlands.Global.ramifiedTwistIsolation.{u}` in [RamifiedTwistIsolationProof.lean](../../Langlands/Global/Arithmetic/RamifiedTwistIsolationProof.lean) ([explanation](../../Langlands/Global/Arithmetic/RamifiedTwistIsolationProof.md)) | `50126e1b2b20b62d408b52dc3552f01089dd1d11` |
| Coherent finite-character prescription, `Langlands.Global.characterPrescription.{u}` in [CharacterPrescriptionAggregateProof.lean](../../Langlands/Global/Arithmetic/CharacterPrescriptionAggregateProof.lean) ([explanation](../../Langlands/Global/Arithmetic/CharacterPrescriptionAggregateProof.md)) | `50126e1b2b20b62d408b52dc3552f01089dd1d11` |
| Conjugate-self-dual finite-order CM prescription, `Langlands.Global.cmFiniteCharacterPrescription.{u}` in [CMFiniteCharacterPrescriptionProof.lean](../../Langlands/Global/Arithmetic/CMFiniteCharacterPrescriptionProof.lean) ([explanation](../../Langlands/Global/Arithmetic/CMFiniteCharacterPrescriptionProof.md)) | `819ea8d4de6f7dde4b0d7f879f58af405e135acf` |
| Regular CM infinity type with prescribed unit components, `Langlands.Global.cmRegularUnitPrescription.{u,v}` in [CMRegularUnitPrescriptionProof.lean](../../Langlands/Global/Arithmetic/CMRegularUnitPrescriptionProof.lean) ([explanation](../../Langlands/Global/Arithmetic/CMRegularUnitPrescriptionProof.md)) | `819ea8d4de6f7dde4b0d7f879f58af405e135acf` |
| Coherent CM-character globalization, `Langlands.Global.cmCharacterGlobalization.{u,v}` in [CMCharacterGlobalizationProof.lean](../../Langlands/Global/Arithmetic/CMCharacterGlobalizationProof.lean) ([explanation](../../Langlands/Global/Arithmetic/CMCharacterGlobalizationProof.md)) | `50126e1b2b20b62d408b52dc3552f01089dd1d11` |
| Field realization and split auxiliary quadratics, `Langlands.Global.fieldRealization.{u,v}` in [FieldRealizationAggregateProof.lean](../../Langlands/Global/Arithmetic/FieldRealizationAggregateProof.lean) ([explanation](../../Langlands/Global/Arithmetic/FieldRealizationAggregateProof.md)) | `819ea8d4de6f7dde4b0d7f879f58af405e135acf` |

The Harris theorem proves the unchanged
`Langlands.Global.HarrisGeneralPositionStatement.{u}` in one arbitrary field
universe. It applies the published reduction
`auxiliaryGeneralPositionReduction` to `auxiliaryCharacterFirstOrder` with equal
field universes. All three conjuncts are retained, for every p-adic field F
and every extension F' of F: a Weil-subgroup character with exact stabilizer
is in general position, which includes its prime-cyclic tower; for every
supplied normalized reciprocity family and every bound r there is a
finite-order character of the units of F' of conductor at least r whose Weil
character has the exact stabilizer; and, under the same hypotheses, there is
one whose Weil character is in general position. Residue characteristic two is
included. The reciprocity
family and its `NormalizedReciprocity` certificate remain explicit hypotheses.
The theorem constructs no such family and does not discharge the separate
normalized-system existence statement.

The ramified twist isolation theorem proves the unchanged
`Langlands.Global.RamifiedTwistIsolationStatement.{u}`. For every number field,
every pair of disjoint finite sets S and T of finite places (empty sets
included), every family of finite-order local characters on S and every depth
function on T, it gives a finite-order Hecke character with exactly the
prescribed components on S, trivial infinity component, and finite component
at each place of T nontrivial on the actual principal units of the requested
depth. The proof applies `ramifiedTwistIsolationOfInputs` to the published
finite-order prescription and arbitrary-ramification theorems.

The character prescription theorem proves the unchanged
`Langlands.Global.CharacterPrescriptionStatement.{u}`, the conjunction of
finite-order prescription (with the order bound 2n and the whole infinity
component), arbitrarily ramified finite-order local characters, and ramified
twist isolation. Each conjunct is a published theorem or, for isolation, the
same application as above. The CM infinity-type and general-position inputs
are separate statements.

The CM finite-order theorem proves the unchanged
`Langlands.Global.CMFiniteCharacterPrescriptionStatement.{u}`. For every CM
field and every finite set S of finite places disjoint from its image under the
actual complex conjugation, every family of finite-order local characters on S
is the family of finite components of a finite-order, conjugate-self-dual Hecke
character with trivial infinity component. The proof applies
`cmFiniteCharacterPrescriptionOfFiniteOrder` to
`finiteOrderCharacterPrescription_proof`.

The regular CM theorem proves the unchanged
`Langlands.Global.CMRegularUnitPrescriptionStatement.{u,v}` with the field
universe and the imaginary-quadratic universe independent. For an anticyclotomic
integral infinity type with distinct weights above a fixed imaginary-quadratic
embedding, and continuous characters of the actual integral units at a finite
set of places disjoint from its conjugate, it gives one positive scaling m and a
conjugate-self-dual Hecke character with infinity type m times the given type,
still with distinct weights, whose finite components restrict to the given unit
characters. Uniformizer values are not prescribed. The proof discharges the
three premises of `cmRegularUnitPrescriptionOfInputs` with the published
unramified-infinity realization, finite-order CM prescription and integral-unit
extension theorems.

The CM globalization theorem proves the unchanged
`Langlands.Global.CMCharacterGlobalizationStatement.{u,v}`, the conjunction of
unramified infinity realization, finite-order CM prescription, integral-unit
character extension and the regular unit prescription, by the same published
terms. The auxiliary local norm-stabilizer construction is not part of this
proposition.

The field realization theorem proves the unchanged
`Langlands.Global.FieldRealizationStatement.{u,v}`, the conjunction of the
totally-real Galois realization (`totallyRealGaloisRealization`) and the split
auxiliary quadratic fields (`splitAuxiliaryQuadratics`) of Henniart (2000)
§3.3. It does not construct the later CM composita, the intermediate-field
tower or paired completion data.

With these proofs every H2 aggregate composition of the field
realization, character prescription, CM-character and Harris rows is in the Library. The Brauer
route for Henniart (2000) §3.7 (p.451) is the
remaining finite-group input. Its targets are
`Langlands.FiniteCharacterTheoryStatement.{uG,uV,uW}` in
`Langlands/Representation/Finite/CharacterStatement`, and the conjuncts of
`Langlands.FiniteRep.FiniteBrauerTheoryStatement.{uG}`, and that aggregate
itself, in `Langlands/Representation/Finite/BrauerStatement`. All are proved in the Library:

- Finite character theory, `Langlands.FiniteCharacterTheoryStatement`: proved, as
  `finiteCharacterTheory` (`Langlands/Representation/Finite/CharacterTheoryProof.lean`); it
  first appeared at Library commit `73016647c403b942bebe18fad4e569a83c342b52`.
- Induced character formula, `Langlands.FiniteRep.FiniteInducedCharacterFormulaStatement`
  (with the rank-one order and induced degree as named theorems): proved, as
  `inducedCharacterFormula` (`Langlands/Representation/Finite/InducedCharacterProof.lean`); it
  first appeared at the same commit.
- Irreducible basis, `Langlands.FiniteRep.FiniteIrreducibleBasisStatement` (with
  virtual-character faithfulness as a named theorem; its proof uses finite character theory):
  proved, as `irreducibleBasis` (`Langlands/Representation/Finite/VirtualCharacterProof.lean`).
- Character lattice, `Langlands.FiniteRep.IntegralBrauerCharacterLatticeStatement` (its proof
  uses the induced character formula): proved, as `characterLattice`
  (`Langlands/Representation/Finite/BrauerLatticeProof.lean`).
- Aggregate, `Langlands.FiniteRep.FiniteBrauerTheoryStatement`, whose new conjunct is
  integral Brauer spanning, built on the three results above: proved, as `finiteBrauerTheory`
  (`Langlands/Representation/Finite/BrauerTheoryProof.lean`).

The explicit
normalized-reciprocity premise, the Galois-side global functional equation, the
CM and tower adapters of the Harris input, and the global field/tower,
Hecke-character, H3 and general automorphic obligations remain.

## Henniart's Harris datum chain and the Brauer proofs

This section was checked on 6 November 2026 against Library
`63d0c9b9d2720e646aa7abb360a08988aee052bf`. The irreducible
basis first appeared in the Library at commit `92a7435d25d4da775fd9c410ea9239236a0eec90`, the
character lattice at `8fb2236bacd54b43eeb9b2fabc30476fee771e05`, and the
Brauer aggregate at `8b3ba080b2e8bcecb1612373f236b9ad96423d12`. The common
base first appeared at `1eb9a9ee0815224a368f8dc58b7d95f024cfff05`, and the
weight-one CM characters at `80f702330eab13242c1eb52eee2757a5d07eb1ba`. For
each of these five proofs, the build and target check passed with the statement unchanged. No
proof adds a hypothesis or an axiom.

| Theorem |
| --- |
| Irreducible basis, `Langlands.FiniteRep.VirtualCharacter.irreducibleBasis` (with `faithfulness` and `faithfulnessAndBasis`) in [VirtualCharacterProof.lean](../../Langlands/Representation/Finite/VirtualCharacterProof.lean) ([explanation](../../Langlands/Representation/Finite/VirtualCharacterProof.md)) |
| Integral character lattice, `Langlands.FiniteRep.BrauerLattice.characterLattice` in [BrauerLatticeProof.lean](../../Langlands/Representation/Finite/BrauerLatticeProof.lean) ([explanation](../../Langlands/Representation/Finite/BrauerLatticeProof.md)) |
| Finite Brauer theory, `Langlands.FiniteRep.BrauerTheory.finiteBrauerTheory` (with `spanning`) in [BrauerTheoryProof.lean](../../Langlands/Representation/Finite/BrauerTheoryProof.lean) ([explanation](../../Langlands/Representation/Finite/BrauerTheoryProof.md)) |
| Common CM base for all intermediate fields, `Langlands.Global.henniartCommonBaseRealization.{uF}` in [HenniartCommonBaseRealizationProof.lean](../../Langlands/Global/Arithmetic/HenniartCommonBaseRealizationProof.lean) ([explanation](../../Langlands/Global/Arithmetic/HenniartCommonBaseRealizationProof.md)) |
| Conjugate-inverse weight-one CM characters, `Langlands.Global.cmHalfWeightCharacter.{u}` in [CMHalfWeightCharacterProof.lean](../../Langlands/Global/Arithmetic/CMHalfWeightCharacterProof.lean) ([explanation](../../Langlands/Global/Arithmetic/CMHalfWeightCharacterProof.md)) |

The three Brauer proofs complete the finite-group input of Henniart (2000)
§3.7 (p.451). The target pair `Langlands/Representation/Finite/BrauerStatement`
is unchanged. The irreducible basis
theorem proves `FiniteIrreducibleBasisStatement G`: the linear map sending
integer coefficients on the actual irreducible classes to the corresponding
element of the virtual representation group is bijective.
The same module proves virtual-character faithfulness and the conjunction of
both. The lattice theorem proves `IntegralBrauerCharacterLatticeStatement G`:
the integer span of the characters of inductions of rank-one data equals the
image of the virtual representation group under the character map, as an
equality and not only up to finite index. Its proof uses the Library's port of the Anthropic FLT
Brauer-induction development (`BrauerTrace` and `SolomonInduction` in
`Langlands/Representation/Finite/`; provenance and licence in
[BrauerTrace.md](../../Langlands/Representation/Finite/BrauerTrace.md)). The aggregate theorem proves
`FiniteBrauerTheoryStatement G` for every finite group `G` in universe `uG`,
the conjunction of all seven conjuncts. Its new conjunct is integral Brauer
spanning (`IntegralBrauerSpanningStatement G`, surjectivity of the expansion in
rank-one inductions), proved from the lattice equality and faithfulness. With
the finite character theory and the induced character formula
of the previous section, all five Brauer targets are proved.

The datum chain makes Harris's Proposition 4.8 hypotheses available on one CM
base field, as Henniart (2000) §§3.3–3.7 requires. Its three statement modules are:

- `Langlands/Global/Arithmetic/HenniartHarrisDatumStatement`. It defines
  `Harris.IsPairedPlaceConfiguration`,
  `HarrisDatumCharacterRealizationStatement`,
  `HenniartCommonBaseRealizationStatement` and `HenniartHarrisDatumStatement`. It first appeared
  at Library commit `86cf8f8984679ba48ded6fa152c55ec38b532d97`.
- `Langlands/Global/Arithmetic/CMHalfWeightCharacterStatement`, defining
  `CMHalfWeightCharacterStatement`; first appeared at the same commit.
- `Langlands/Global/Arithmetic/HenniartHarrisDatumReductionStatement`. It defines the two
  implications
  `HarrisDatumCharacterRealizationOfHalfWeightStatement` and
  `HenniartHarrisDatumOfHalfWeightStatement`, each with
  `CMHalfWeightCharacterStatement` as premise. It first appeared at
  `8b3ba080b2e8bcecb1612373f236b9ad96423d12`.

The common-base theorem proves the unchanged
`HenniartCommonBaseRealizationStatement.{uF}`. For every prime p, every p-adic
field F and every finite extension M of F, it gives one CM number field E, a
finite place v₀ of E and a ring isomorphism ι₀ from the completion of E at v₀
to F, continuous in both directions. These are chosen before the intermediate
field. Every intermediate field F' of M/F then has a paired-place configuration
over E whose place `P.v` is v₀ and whose `P.iso` agrees with ι₀ on E. The proof
refines the published single-extension construction: it fixes the F-algebra
structure of the auxiliary Galois extension through the normal closure of M,
so the base field and its place do not depend on F'. No Galois hypothesis on M
and no restriction on p is assumed.

The weight-one theorem proves the unchanged
`CMHalfWeightCharacterStatement.{u}`. For every CM number field K, every
integral infinity type t of pure weight one and every finite set S of finite
places disjoint from its image under complex conjugation, it gives a Hecke character
φ with conjugate-inverse symmetry, with φ at infinity times the product of the
complex absolute values equal to the character of t, and unramified at every
place of S. The source is Harris–Taylor (2001), proof of Corollary VII.2.8.
The proof constructs the character on an open subgroup and extends it from the
quotient by the norm and support classes. Its finite-norm sign step uses the
Library's `CMFiniteNormSign`, which derives the reciprocity input from proved
local class formation, global reciprocity and idele-class H1 vanishing, so no
class-field premise remains. The proof imports the helper modules
`CMHalfWeightInfinity`, `CMHalfWeightRealSign`, `CMHalfWeightNormInfinity`,
`CMHalfWeightFiniteControl`, `CMHalfWeightLocalNormControl` and
`CMHalfWeightExtension`, which are in the same Library directory.

Three further steps complete the datum chain; all are proved in the Library.

- Character realization, `HarrisDatumCharacterRealizationOfHalfWeightStatement`: proved, as
  `harrisDatumCharacterRealizationOfHalfWeight`
  (`Langlands/Global/Arithmetic/HarrisDatumCharacterRealizationProof.lean`), with the modules
  `HarrisDatumArchimedean`, `HarrisDatumLocal` and `HarrisDatumAuxiliary`. The route multiplies the regular CM
  character of the published `cmRegularUnitPrescription` by a weight-one
  character from the premise when `[E' : E]` is even. The auxiliary character
  comes from the published `auxiliaryCharacterFirstOrder`, and general position
  from the published transport and exact-stabilizer theorems.
- Datum reduction, `HenniartHarrisDatumOfHalfWeightStatement`: proved, as
  `henniartHarrisDatumOfHalfWeight`
  (`Langlands/Global/Arithmetic/HenniartHarrisDatumReductionProof.lean`). It uses the common base
  and the character realization, and applies the common base and then the character realization at universe
  `0`.
- Harris datum, `HenniartHarrisDatumStatement`: proved, as `henniartHarrisDatum`
  (`Langlands/Global/Arithmetic/HenniartHarrisDatumProof.lean`), the
  reduction applied to `cmHalfWeightCharacter`. The module also proves the
  unconditional `HarrisDatumCharacterRealizationStatement`, as
  `harrisDatumCharacterRealization`, which is not part of the target.

The datum statement keeps the normalized reciprocity family as
a universally quantified hypothesis; it constructs no such family. Harris's
Proposition 4.8 itself (`Langlands.Global.Harris.Proposition48Statement`) has only the
conditional proof `proposition48_of_hasSolution`
(`Langlands/Global/Arithmetic/HarrisProposition48ReductionProof.lean`) in the Library. The Hecke
global functional equation (`Langlands.Global.HeckeGlobalFunctionalEquationStatement`) is
proved, as `heckeGlobalFunctionalEquation_proof`
(`Langlands/Global/Factors/HeckeFunctionalEquationProof.lean`). The Galois-side global
functional equation, the global field/tower, H3 and general automorphic obligations remain.

## Bernstein–Lapid §§2–3: statements and definitions

This section was checked on 10 November 2026 against Library
`e748734106ab2ee9de1cab1eb18a60e59593aac0`. The H1 rows of the earlier sections record an
earlier state; this section does not recertify them.

### Public statements and definitions

| Module | First appeared at Library commit | Exact content and boundary |
| --- | --- | --- |
| [QuotientConvolutionKernelStatement](../../Langlands/Analysis/Local/QuotientConvolutionKernelStatement.md) | `d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8` | `Langlands.QuotientIntegration.QuotientConvolutionKernelStatement`: continuous kernel vectors and the support bound for compactly supported convolutions on a coset space. The Library proves it, as `quotientConvolutionKernel` (`Langlands/Analysis/Local/QuotientConvolutionKernelProof.lean`). |
| [ContinuationPrincipleStatement](../../Langlands/Analysis/Meromorphic/ContinuationPrincipleStatement.md) with helper [AnalyticSystems](../../Langlands/Analysis/Meromorphic/AnalyticSystems.md) | `58a91d4ff65b8d6dcb8aa417bfc63399feb8b4af` | Bernstein–Lapid (BL) §§3.1–3.3 and Theorem 3.3, pp.192–194: weak holomorphy, local common-denominator meromorphy, analytic systems, local finite type. `MeromorphicContinuationPrincipleStatement` is the conjunction of `MeromorphicContinuationHolomorphicStatement` (openness, holomorphy, meromorphy) and `MeromorphicContinuationAnalyticComplementStatement`. The Library proves both conjuncts, as `meromorphicContinuationHolomorphic` (`Langlands/Analysis/Meromorphic/ContinuationPrincipleHolomorphicProof.lean`) and `meromorphicContinuationAnalyticComplement` (`Langlands/Analysis/Meromorphic/ContinuationPrincipleAnalyticComplementProof.lean`); this note records no theorem stating the conjunction itself. |
| [FredholmCriterionStatement](../../Langlands/Analysis/Meromorphic/FredholmCriterionStatement.md) | `58a91d4ff65b8d6dcb8aa417bfc63399feb8b4af` | BL §3.4, pp.194–195: `FredholmCriterionStatement` (Banach spaces, left invertible modulo compact operators) and `HilbertFredholmCriterionStatement` (Corollary 3.4); their conjunction `FredholmFiniteTypeStatement`. The Library proves all three, as `fredholmCriterion`, `hilbertFredholmCriterion` and `fredholmFiniteType` (`Langlands/Analysis/Meromorphic/FredholmCriterionProof.lean`). |
| [AdelicComplexParameters](../../Langlands/Global/AdelicComplexParameters.md) with helper [LinearCoordinates](../../Langlands/Analysis/Meromorphic/LinearCoordinates.md) | `e748734106ab2ee9de1cab1eb18a60e59593aac0` | BL §2.1, p.190: `ComplexCharacterParameter F G = ℂ ⊗[ℤ] X^*(G)`, its pairing with the existing `RealCharacterDual`, the real part, and `parameterCharacter`, `m ↦ m^λ = exp ⟨λ, characterLog m⟩`. `IsHolomorphicInCoordinatesOn` and `IsMeromorphicInCoordinatesOn` express holomorphy and meromorphy on such parameter spaces in every complex linear coordinate system. Definitions only. |

The conditions of Mœglin–Waldspurger
I.2.17 for functions on `G(𝔸)` left invariant under an arbitrary subgroup `Γ`
(module `Langlands.Automorphic.GroupSchemeInvariantForms`), for BL's
`𝒜_P` with `Γ = U(𝔸)M(F)`, and their agreement for `Γ = G(F)` with
the existing `IsAdelicAutomorphicForm`, are treated in the next section.

### Proof targets and their routes

| Exact target | Recorded route or obstacle | Proof in the Library |
| --- | --- | --- |
| `Langlands.Analysis.IntegratedActionConvolutionStatement` | A complete proof had been written and compiled without errors or warnings. | `integratedActionConvolution` (`Langlands/Representation/Unitary/IntegratedConvolutionProof.lean`) |
| `Langlands.QuotientIntegration.QuotientConvolutionKernelStatement` | A complete proof had been written and compiled. | `quotientConvolutionKernel` (`Langlands/Analysis/Local/QuotientConvolutionKernelProof.lean`) |
| `Langlands.Analysis.Meromorphic.FredholmFiniteTypeStatement`, with both conjuncts | The pinned Mathlib has Fredholm operators but no lemma that identity minus compact is Fredholm, and no passage from weak to norm holomorphy of operator families. | `fredholmFiniteType` (`Langlands/Analysis/Meromorphic/FredholmCriterionProof.lean`) |
| `Langlands.Analysis.Meromorphic.MeromorphicContinuationHolomorphicStatement` | Holomorphy of compositions needs Hartogs's theorem on separate holomorphy (BL p.193), absent from Mathlib. The identity theorem can replace connectedness of hypersurface complements. | `meromorphicContinuationHolomorphic` (`Langlands/Analysis/Meromorphic/ContinuationPrincipleHolomorphicProof.lean`) |
| `Langlands.Analysis.Meromorphic.MeromorphicContinuationAnalyticComplementStatement` | Reducing a possibly infinite family of determinants to finitely many local equations needs the theorem that an arbitrary intersection of analytic subsets is analytic. The statement's Markdown attributes this to Noetherianity of convergent power series; Noetherianity of the local ring alone does not give one common neighborhood. | `meromorphicContinuationAnalyticComplement` (`Langlands/Analysis/Meromorphic/ContinuationPrincipleAnalyticComplementProof.lean`) |

Further proof targets of the earlier sections: pointwise
representatives (`IntegratedTranslationPointwiseStatement`, proved as
`integratedTranslationPointwise`, `Langlands/Representation/Unitary/IntegratedTranslationPointwiseProof.lean`),
discrete decomposition of invariant subspaces (`InvariantSubspaceDiscreteDecompositionStatement`,
proved as `invariantSubspaceDiscreteDecomposition`,
`Langlands/Representation/Unitary/InvariantSubspaceDiscreteDecompositionProof.lean`), the smooth
inverse kernel sequence (`SmoothInverseKernelSequenceStatement`, proved as
`Langlands.Analysis.smoothInverseKernelSequence`), the full almost-everywhere finite
approximation on the positive-torus quotient, finite ramification of Hecke characters
(`HeckeFiniteRamificationStatement`; this note records no proof) and Hecke local rigidity
(`HeckeLocalComponentRigidityStatement`, proved as `heckeLocalComponentRigidity`,
`Langlands/Automorphic/Unramified/HeckeLocalComponentRigidityProof.lean`). Further
compact-quotient and cuspidal proofs use these results.

### L1/L2 interface

The division between L1 and L2 is as follows. `𝔞_M` and `H_M`
are the published `RealCharacterDual` and `characterLog`. L1 builds the
Iwasawa height `H_P` for every standard parabolic relative to one supplied
compact `K` with `P(𝔸)K = G(𝔸)`, and the quotient `X_P = U(𝔸)M(F) \ G(𝔸)`.
L2 builds the parameter space and `m ↦ m^λ`, the space `𝒜_P`, the
Eisenstein series, the intertwining operators and the topology of the space of
functions of uniform moderate growth of BL §7. The L1 height module is
`AdelicIwasawaHeight` (see the [L1 note](l1-reductive-quotient-measure-coverage.md), §3).

Neither track of the program is complete. The L2 continuation, functional
equation and Eisenstein-series statements are described in the next section.

## Bernstein–Lapid §2 statements

This section was checked on 11 November 2026 against Library
`0ef479821d752edef9ef540203ddfb7f637bbce6`.

### Further public modules

Helper modules are listed with the module that introduced them.

| Module | Exact content and boundary |
| --- | --- |
| [GroupSchemeInvariantFormsComparisonStatement](../../Langlands/Automorphic/GroupSchemeInvariantFormsComparisonStatement.md) with helper [GroupSchemeInvariantForms](../../Langlands/Automorphic/GroupSchemeInvariantForms.md) | Mœglin–Waldspurger (MW) I.2.17 for functions on `G(𝔸)` left invariant under an arbitrary subgroup `Γ` (`IsAutomorphicFunctionOn`); for `Γ = U(𝔸)M(F)` this is BL's `𝒜_P`. The statement asserts agreement with the existing `IsAdelicAutomorphicForm` for `Γ = G(F)`. The Library proves it, as `rationalAutomorphicFunctionComparison` (`Langlands/Automorphic/GroupSchemeInvariantFormsComparison.lean`). |
| [GroupSchemeUniformGrowthFrechet](../../Langlands/Automorphic/GroupSchemeUniformGrowthFrechet.md) | Derived from BL §7.1, pp.210–211: the Fréchet space `UniformGrowthFrechetSpace … hN hrho R L` of right `L`-invariant smooth functions of uniform moderate growth with exponent `R`, weighted through a closed matrix embedding `rho`. It agrees with BL's space only up to a change of exponent (explained, not proved, in the Markdown). The LF-topology on `𝔉_umg` is not constructed. Definitions only. |
| [AdelicEisensteinConvergenceStatement](../../Langlands/Global/AdelicEisensteinConvergenceStatement.md) with helper [AdelicEisensteinSeries](../../Langlands/Global/AdelicEisensteinSeries.md) | BL (2.1), p.191, and MW II.1.5, p.85: `m_P^λ`, `φ_λ`, the series `E(g, φ, λ) = Σ_{P(F)\G(F)} φ_λ(γg)`, the regularity predicate `IsRegularParameter` and `EisensteinAbsoluteConvergenceStatement` (normal convergence for `g` in compacts and `λ` in compacts of a translate of the positive cone). |
| [AdelicEisensteinContinuationStatement](../../Langlands/Global/AdelicEisensteinContinuationStatement.md) | BL Theorem 2.3 (1) in the Fréchet form of the Corollary in §8.6, p.226: `EisensteinMeromorphicContinuationStatement`. |
| [AdelicIntertwiningConvergenceStatement](../../Langlands/Global/AdelicIntertwiningConvergenceStatement.md) with helper [AdelicIntertwiningOperator](../../Langlands/Global/AdelicIntertwiningOperator.md) | MW II.1.6, pp.87–88, and BL §2.2: `w λ`, the Weyl presentation `IsWeylConjugation`, the operator `M(w, λ)φ` on actual adelic points, and `IntertwiningAbsoluteConvergenceStatement` (domination by an integrable function on a region smaller than BL's). |
| [AdelicIntertwiningContinuationStatement](../../Langlands/Global/AdelicIntertwiningContinuationStatement.md) | BL Theorem 2.3 (3): `M(w, λ)φ` continues meromorphically within a finite-dimensional subspace of `𝒜_Q`. |
| [AdelicEisensteinFunctionalEquationStatement](../../Langlands/Global/AdelicEisensteinFunctionalEquationStatement.md) | BL Theorem 2.3 (4), universal over continuation data: `E(φ, λ) = E(M(w, λ)φ, wλ)` on the intersection of the domains. |
| [AdelicIntertwiningCocycleStatement](../../Langlands/Global/AdelicIntertwiningCocycleStatement.md) | BL Theorem 2.3 (5), universal over continuation data: `M(w'w, λ) = M(w', wλ) M(w, λ)`. |
| [AdelicRootHyperplaneStatement](../../Langlands/Global/AdelicRootHyperplaneStatement.md) | BL Theorem 2.3 (6), first sentence, in the local product form of the Corollary in §8.6: singularities of `M(w, λ)φ` and `E(φ, λ)` lie along root hyperplanes. |

The clause of BL Theorem 2.3 (1) that a regular value of the continuation is
an automorphic form is a conjunct of the continuation statement. BL Theorem
2.3 (2) and the rationality clause of 2.3 (3) concern function fields and are
not formalized; all statements above assume a number field.

### Further proof targets and their routes

| Exact target | Recorded route or obstacle | Proof in the Library |
| --- | --- | --- |
| `Langlands.Global.WeilPairPoleRegionStatement` (Henniart 1986, 4.5 (i)) | H1 analytic input. | `weilPairPoleRegionStatement` (`Langlands/Global/Factors/WeilPoleRegionProof.lean`) |
| `Langlands.Global.GLPairPoleRegionStatement` (Henniart 1986, 4.5 (ii)) | Needs Jacquet–Piatetski-Shapiro–Shalika L-factor computations, which the Library lacked when this route was recorded. | `glPairPoleRegion` (`Langlands/Global/Factors/GLPoleRegionProof.lean`) |
| `Langlands.Global.EisensteinAbsoluteConvergenceStatement` | Moderate growth, comparison of heights on Siegel sets, Godement's convergence of `Σ m_P(γg)^ν`. | `eisensteinAbsoluteConvergence` (`Langlands/Global/AdelicEisensteinConvergenceProof.lean`) |
| `Langlands.Global.EisensteinMeromorphicContinuationStatement` | BL §§4–8: the system `Ξ_fnl(λ)`, uniqueness through leading cuspidal components (§6), finite type (§7), and the continuation principle (`FredholmFiniteTypeStatement`, `MeromorphicContinuationHolomorphicStatement`, `MeromorphicContinuationAnalyticComplementStatement`). | none recorded; conditional: `eisensteinMeromorphicContinuation_of_analyticSystem` (`Langlands/Global/AdelicEisensteinContinuationReduction.lean`) |
| `Langlands.Global.IntertwiningAbsoluteConvergenceStatement` | Unfolding against the normal convergence of the Eisenstein series (MW II.1.6). | `intertwiningAbsoluteConvergence` (`Langlands/Global/AdelicIntertwiningConvergenceProof.lean`) |
| `Langlands.Global.IntertwiningMeromorphicContinuationStatement` | Constant terms of the continued Eisenstein series (BL Lemma 6.10, Corollary in §8.6). | none recorded; conditional: from `IntertwiningFiniteSpanStatement` and `IntertwiningWeakMeromorphicContinuationStatement` (`intertwiningMeromorphicContinuationReduction`, `Langlands/Global/AdelicIntertwiningContinuationReduction.lean`) |
| `Langlands.Global.EisensteinFunctionalEquationStatement` | The `P`-regular and `wλ`-regular regions are in general disjoint, so the identity needs BL's uniqueness through leading terms (§6), not only convergent series. | none recorded; conditional: from `EisensteinFunctionalEquationRegularComparisonStatement` (`eisensteinFunctionalEquationRegularComparisonReduction`, `Langlands/Global/AdelicEisensteinFunctionalEquationRegularComparisonReduction.lean`) |
| `Langlands.Global.IntertwiningCocycleStatement` | BL deduce it from 2.3 (4) and injectivity (8.4); a direct Fubini argument covers only pairs whose lengths add. | none recorded; conditional: `intertwiningCocycle_of_inputs` (`Langlands/Global/AdelicIntertwiningCocycleReduction.lean`) |
| `Langlands.Global.RootHyperplaneSingularitiesStatement` | BL Corollary in §8.6. | none recorded; conditional: from `RootHyperplaneContinuationStatement` and the proved `PositiveChamberNonemptyStatement` (`rootHyperplaneReduction`, `Langlands/Global/AdelicRootHyperplaneReduction.lean`) |

Neither track of the program is complete. The table gives the Bernstein–Lapid proofs in the
Library. The constant term of Eisenstein series (MW II.1.7, BL Lemma 6.10) is stated in the
next section; the
`W(P, Q)` double-coset bookkeeping beyond single presentations and the
LF-topology on `𝔉_umg` were not stated at this commit.

## The constant term of Eisenstein series and the L3 block

This section was checked on 11 November 2026 against Library
`63d9b857523edf47443b7bf30844159e526d00b0`.

| Module | Exact content and boundary |
| --- | --- |
| [AdelicEisensteinConstantTermStatement](../../Langlands/Global/AdelicEisensteinConstantTermStatement.md) | BL Lemma 6.10, formula (6.17), pp.208–209, and MW II.1.7, pp.91–93, without cuspidality: `EisensteinConstantTermStatement`. For arbitrary rational double-coset representatives `w_i` of `Q(F)\G(F)/P(F)` and parabolics `P'_i`, `Q'_i` described by their rational points, the constant term of `E(φ, λ)` along `Q` is the sum of the intertwining integrals of the constant terms of `φ` along `P'_i`, with integrability and summability conjuncts. Helpers: `rationalImage`, `RelativeRationalCosets`, `subgroupConstantTerm` (the measure divides by the total mass and is zero at infinite mass), `parameterRestrict`, `IsDoubleCosetRepresentatives`, `IsGeometricLemmaDatum`. Formula (6.18) for the cuspidal projection is not stated. |

The proof of `Langlands.Global.EisensteinConstantTermStatement` follows BL's unfolding over
the given representatives and needs the absolute convergence of Eisenstein series
(`EisensteinAbsoluteConvergenceStatement`, proved, see above). The Library has the conditional
proof `eisensteinConstantTerm_of_convergence_of_unfolding`
(`Langlands/Global/EisensteinConstantTerm/Reduction.lean`); this note records no unconditional
proof.

The L3 block consists of parabolic combinatorics (`τ_P`, `τ̂_P`, `σ`, Langlands' `φ_P(Λ, H)`,
Arthur 1978 Proposition 1.1 and Lemmas 6.1 and 6.3), `(G, M)`-families
(Arthur 2005, Lemmas 17.1 and 17.4–17.6) and Arthur truncation (Lemma 8.2,
Propositions 13.1–13.3). The Library had none of these at this commit; they are described in
[Arthur L3 foundations](arthur-l3-foundations-coverage.md).

Neither track of the program is complete.
The `W(P, Q)` bookkeeping beyond single presentations, the LF-topology on
`𝔉_umg` and the Lapid 2011 spectral statements were not stated at this commit.

## Lapid 2011 Propositions 2 and 6

This section was checked on 11 November 2026 against Library
`4ed6d9794db38a5178b5c7ab6b048b42eff9d907`. Two of the Lapid 2011 spectral statements
are stated here. The source is E. Lapid, *On Arthur's asymptotic inner product
formula of truncated Eisenstein series*, Clay Math. Proc. 13 (2011),
pp. 309–331, registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`.

Both modules below are
stated for number fields `F : Type` (universe zero), because the canonical
split-centre interface they use is stated in that universe.

| Module | Exact content and boundary |
| --- | --- |
| [AdelicEisensteinImaginaryHolomorphyStatement](../../Langlands/Global/AdelicEisensteinImaginaryHolomorphyStatement.md) with helper [AdelicSquareIntegrableInducedForms](../../Langlands/Global/AdelicSquareIntegrableInducedForms.md) | Lapid Proposition 6, pp.329–330, in scalar form: `EisensteinImaginaryAxisHolomorphyStatement`. For every continuation `(E, D)` of the Eisenstein series of a vector of `A^2_P` there is a continuation `(E', D')` with `i𝔞_P^* ⊆ D'`, meromorphic in every `g` on the one domain `D'`, that agrees with `E` on `D ∩ D'`. Helpers: `imaginaryParameter`, `modulusParameter`, `halfModulusParameter` (`ρ_P`), `IsSplitComponentEquivariant` (`A^n_P`) and `IsSquareIntegrableInducedForm` (`A^2_P`). Fréchet-valued holomorphy is not asserted. |
| [AdelicWavePacketInnerProductStatement](../../Langlands/Global/AdelicWavePacketInnerProductStatement.md) with helper [AdelicInducedInnerProduct](../../Langlands/Global/AdelicInducedInnerProduct.md) | Lapid Proposition 2, pp.313–314: `WavePacketInnerProductStatement`. Wave packets `Θ` of square-integrable inducing data are in `L²(G(F) \ G(𝔸))`, and their inner product is `∫ Σ_{w ∈ Ω(P, P')} (M(w, λ)φ(λ), φ'(wλ))_{P'} dλ`. The data are globally regular: every generating Eisenstein continuation and every intertwining coefficient must be meromorphic on a domain containing all of `i𝔞_P^*`. Helpers: `parameterCoordinates`, `spectralMeasure`, `IsIwasawaCompatibleMeasure`, the `β`-weighted inner product `inducedInnerProduct`, `realWeylParameter` and `weylParameterSet` (`W(𝔞_M, 𝔞_{M'})`). The Hilbert space `L`, the isometry of Lapid Theorem 2 and surjectivity are not stated. |

The second statement has a boundary. Because it requires
regularity on all of `i𝔞_P^*`, it cannot serve as the input to Lapid's own proof
of Proposition 6. That proof uses Lemma 10: wave packets of bounded measurable
data supported in a compact set on which the Eisenstein series are regular,
with the bound `‖Θ_φ‖² ≤ |Ω| ‖φ‖²_*`. Lemma 10 was not stated at this commit (see the next
section).


| Exact target | Recorded route or obstacle | Proof in the Library |
| --- | --- | --- |
| `Langlands.Global.WavePacketInnerProductStatement` | Lapid §8, p.328: Lemma 9 (square integrability through `Λ^T`), Proposition 1 (the asymptotic formula (2) and its ingredients in §§4–7), Lemma 8 on `(G, M)`-families, the constant term of Eisenstein series (`EisensteinConstantTermStatement`), MW I.4.11, and the adjointness of `M(w, λ)`. Truncation belongs to the L3 block ([Arthur L3 foundations](arthur-l3-foundations-coverage.md)). | none recorded; conditional: from `LocalWavePacketInnerProductStatement` (`wavePacketInnerProduct_of_local`, `Langlands/Global/AdelicLocalWavePacketStatement.lean`) |
| `Langlands.Global.EisensteinImaginaryAxisHolomorphyStatement` | Lapid §8, pp.329–330: Lemma 10, then a contradiction at a pole of order `k ≥ 1` along a root hyperplane through a point of `i𝔞_P^*`, comparing the growth of `Θ_φ(x_0)` with the bound (19). Bernstein–Lapid Theorem 2.3 supplies Lapid's Working hypothesis. | none recorded; conditional: `eisensteinImaginaryAxisHolomorphy_of_premises` (`Langlands/Global/AdelicEisensteinImaginaryHolomorphyReduction.lean`) |

Three further results are needed: Lapid's Proposition 1 (the truncated asymptotic inner
product), Lemma 10 (the local wave-packet bound) and the unitarity of `M(w, λ)` on
`i𝔞_P^*` (Lapid p.312 and MW IV.3.12). None of these three was stated at this commit.

Neither track of the program is complete. Lapid Proposition 1, Lemma 10 and Theorem 2, the
unitarity of `M(w, λ)` on `i𝔞_P^*`, the `W(P, Q)` bookkeeping beyond single presentations
and the LF-topology on `𝔉_umg` were not stated at this commit.

## Lapid Lemma 10 and Theorem 2, unitarity, Delorme completeness, Getz–Hahn 10.5.1 and the spectral transform

This section was checked on 12 November 2026 against Library
`440a690b5471ae33c2209a6ebc4d5b21e3923b60`. Lapid's Lemma 10 and Theorem 2, the
unitarity of `M(w, λ)` on `i𝔞_P^*`, Delorme's completeness theorem, Getz–Hahn Theorem 10.5.1
and the unitary spectral transform of Arthur's Theorem 7.2 (b) are stated in the Library. All
are stated for number fields `F : Type`. Their proofs are listed in the second table below.

| Module | Exact content and boundary |
| --- | --- |
| [AdelicBoundedWavePacketStatement](../../Langlands/Global/AdelicBoundedWavePacketStatement.md) | Lapid Lemma 10, §8, p.329: `BoundedWavePacketStatement`, the conjunction of the inner-product formula of Proposition 2 for bounded measurable data supported in a compact set where the Eisenstein series and intertwining coefficients are regular, and the bound `‖Θ_φ‖² ≤ |Ω(P, P)| ∫ (φ(λ), φ(λ))_P dλ`. Lapid's `|Ω|` is replaced by the smaller `|Ω(P, P)|` that his proof gives. |
| [AdelicIntertwiningImaginaryUnitarityStatement](../../Langlands/Global/AdelicIntertwiningImaginaryUnitarityStatement.md) | Lapid p.312, Mœglin–Waldspurger IV.1.11 (b), VI.2.1 (i): `IntertwiningImaginaryUnitarityStatement`. If `M(w, λ)v_j = ∑ coeff_{ji}(λ) ψ_{ji}` with `v_j ∈ A^2_P`, `ψ_{ji} ∈ A^2_{P'}` and meromorphic coefficients, there are coefficients holomorphic near `i𝔞_P^*`, giving the same functions, that preserve the inner products `(·,·)_P → (·,·)_{P'}` at imaginary `λ`. The availability of the expansions is a hypothesis. Surjectivity of the Hilbert-space extension is not stated. |
| [AdelicWavePacketIsometryStatement](../../Langlands/Global/AdelicWavePacketIsometryStatement.md) | Lapid Theorem 2, p.314; Arthur Theorem 7.2 (b): `WavePacketIsometryStatement`. For a finite family of presented parabolics with Weyl-compatible wave packet data, `‖∑_i n_i⁻¹ Θ_i‖² = ∑_i n_i⁻¹ ∫ (F_i, F_i)_{P_i} dλ` with `n_i = ∑_{i'} |Ω(P_i, P_{i'})|`. The coordinate changes are assumed measure preserving. The Hilbert space `L` and the extension are not stated here (see the transform below). |
| [AdelicWavePacketCompletenessStatement](../../Langlands/Global/AdelicWavePacketCompletenessStatement.md) | Delorme 2023 Theorem 7.9: `WavePacketCompletenessStatement`. A function in `L²(G(F) \ G(𝔸))` orthogonal to the wave packets of every presented parabolic `P` with `P(𝔸)K = G(𝔸)` vanishes almost everywhere, for `K` with an Iwasawa decomposition for some minimal parabolic. |
| [AdelicSpectralDecompositionStatement](../../Langlands/Global/AdelicSpectralDecompositionStatement.md) with helpers [AdelicParabolicSpectrum](../../Langlands/Global/AdelicParabolicSpectrum.md) and [DiscretePart](../../Langlands/Representation/Unitary/DiscretePart.md) | Getz–Hahn Theorem 10.5.1 on `[G]`: `SpectralDecompositionStatement`. For each minimal `P₀` with `P₀(𝔸)K = G(𝔸)` and the presented standard parabolics `P ⊇ P₀`, the spaces `L²_P([G])` (`parabolicSpectrum`, the closed span of the wave packets over `i(𝔞_M^G)^*`) are finitely many with dense sum, `L²_G([G])` is the discrete spectrum (`discreteSpectrum`, via `Langlands.Analysis.discretePart`), associate parabolics give equal spaces and non-associate ones orthogonal spaces. The unitary transform itself is the next module (`AdelicSpectralTransformStatement`). |
| [AdelicSpectralTransformStatement](../../Langlands/Global/AdelicSpectralTransformStatement.md) with helper [AdelicSpectralTransformSpaces](../../Langlands/Global/AdelicSpectralTransformSpaces.md) | Arthur 2005 Theorem 7.2 (b), Getz–Hahn (10.22)–(10.24), on `L²(G(F) \ G(𝔸))`: `SpectralTransformStatement`. With `H_P` the closure of the restrictions of `A^2_P` (`inducedHilbertSpace`), operators `M(w, i e(x))` on `H_P` characterized by the meromorphic expansions (`IsImaginaryIntertwiningOperator`) exist. For every such choice there is a linear isometry from Arthur's space `L̂` of Weyl-compatible families (`symmetricFamilySpace`) that extends `∑_P n_P⁻¹ ∫ E(F_P(λ), λ) dλ` from the dense smooth compactly supported families and has closed, `G(𝔸)`-invariant range. It does not state that the transform intertwines the right regular representation with `I_P(λ, y)`, nor the identification of its range with Getz–Hahn's `L²_𝒫([G])`. |

These statements have the following boundaries. The two decomposition
statements live on different quotients: the transform and Delorme's
completeness on `G(F) \ G(𝔸)` with parameters in `i𝔞_P^*`, and Getz–Hahn
10.5.1 on `[G]` with parameters in `i(𝔞_M^G)^*`. No comparison between them
is stated. Completeness is stated for the packets of all presented
parabolics, including non-standard ones, while 10.5.1 uses standard ones;
the proof of 10.5.1 must bridge this. The comparison of `inducedHilbertSpace` with Arthur's `H_P` and of
`parabolicSpectrum` with the range of the transform are explanatory, not
proved.


| Exact target | Recorded route or obstacle | Proof in the Library |
| --- | --- | --- |
| `Langlands.Global.BoundedWavePacketStatement` | Lapid p.329: approximate the data by smooth compactly supported data `φ_n` supported near the regular set, use Proposition 2 under local regularity and the unitarity of `M(w, λ)` to show that `Θ_{φ_n}` is Cauchy, and pass to the limit; the bound follows by Cauchy–Schwarz, unitarity and the invariance of `dλ` under `Ω(P, P)`. | none recorded; conditional: `boundedWavePacket_of_local` (`Langlands/Global/BoundedWavePacketReduction.lean`) |
| `Langlands.Global.IntertwiningImaginaryUnitarityStatement` | Mœglin–Waldspurger IV.3.12: adjunction II.1.8, the functional equation `M(w⁻¹, wλ)M(w, λ) = 1`, and root-hyperplane singularities for holomorphy. | none recorded; conditional: `intertwiningImaginaryUnitarity_of_inputs` (`Langlands/Global/AdelicIntertwiningImaginaryUnitarityReduction.lean`) |
| `Langlands.Global.WavePacketIsometryStatement` | Proposition 2 for each pair, the Weyl compatibility and the counting `∑_i n_i⁻¹ |Ω(P_i, P_{i'})| = 1`. | none recorded; conditional: from `WavePacketInnerProductStatement` and the proved `InducedInnerProductIntegrableStatement` (`wavePacketIsometry_of_innerProduct`, `Langlands/Global/AdelicWavePacketIsometryReduction.lean`) |
| `Langlands.Global.WavePacketCompletenessStatement` | Delorme §§3–7: Franke temperedness, uniform temperedness of Eisenstein series, Schwartz-space wave packets (Lapid 2013), Bernstein's temperedness of the spectrum, truncated inner products. These ingredients need their own statements and proofs. | none recorded; conditional: from `SpectralWitnessStatement`, `WavePacketRapidDecayStatement`, `WavePacketOrthogonalTranslationStatement` and `TemperedWavePacketVanishingStatement` (`wavePacketCompleteness_of_reduction`, `Langlands/Global/AdelicWavePacketCompletenessReduction.lean`) |
| `Langlands.Global.SpectralDecompositionStatement` | Orthogonality from Proposition 2, equality from the functional equation and unitarity, density from Delorme 7.9 transferred to `[G]`, `L²_G = L²_disc` classically. | none recorded; conditional: `spectralDecomposition_of_reduction` (`Langlands/Global/AdelicSpectralDecompositionReduction.lean`) |
| `Langlands.Global.SpectralTransformStatement` | Unitarity for the operators, Theorem 2 for the isometry, Delorme Lemma 6.2 symmetrization for density, closedness of isometric images, and right translation through `I_P(λ, y)`. | none recorded; conditional: from `ImaginaryIntertwiningExistenceStatement`, `SymmetricFamilyDensityStatement`, `EisensteinImaginaryContinuationStatement`, `SymmetricFamilyGramStatement` and `WavePacketTranslationStatement` (`spectralTransformReduction`, `Langlands/Global/AdelicSpectralTransformReduction.lean`) |

Two L4 statements are stated in the next section: Getz–Hahn Theorem 11.3.6, the Whittaker
expansion of smooth cuspidal functions of uniform moderate growth on `GL_{r+1}`, and Getz–Hahn
Theorem 11.4.3, cuspidal multiplicity one for `GL_n` on the full almost-everywhere cuspidal
`L²` space. The L4 table row "Whittaker and multiplicity" recorded Cogdell 2007 as missing;
these statements cite Cogdell's 2004 chapter `cogdell-2004-analytic-theory-gln`,
Theorem 1.1, which states the expansion and sketches the same induction.

Neither track of the program is complete. Lapid's Proposition 1 was not stated at this
commit; it needs the truncation block ([Arthur L3 foundations](arthur-l3-foundations-coverage.md)).

## Whittaker expansion, cuspidal multiplicity one, Arthur's combinatorics and Shahidi's Theorem 5.2

This section was checked on 13 November 2026 against Library
`ed924aef420de137b4cbaa3b063a3618afcd73fd`. The two L4 statements announced in the previous
section are stated in the Library, and so are the abstract layer of Arthur's combinatorics and
Shahidi (1981), Theorem 5.2. The last column of the second table gives their proofs.

| Module | First appeared at Library commit | Exact content and boundary |
| --- | --- | --- |
| [GeneralLinearWhittakerExpansionStatement](../../Langlands/Global/GeneralLinearWhittakerExpansionStatement.md) with helper [GeneralLinearGlobalWhittaker](../../Langlands/Global/GeneralLinearGlobalWhittaker.md) | `f59009a7` | Getz–Hahn Theorem 11.3.6, Cogdell 2004 Theorem 1.1, Shalika 1974 Theorem 5.9: `Langlands.Global.WhittakerExpansionStatement`. A smooth (finite level, archimedean plot-smooth) cuspidal function of uniform moderate growth on `GL_{r+1}(F) \ GL_{r+1}(𝔸)` is the absolutely convergent sum of its Whittaker function translated over `N_r(F) \ GL_r(F)`, for a nontrivial character `ψ` trivial on `F` and any generic `m`, and the sum of absolute values converges uniformly on compact sets. |
| [GeneralLinearCuspidalMultiplicityOneStatement](../../Langlands/Automorphic/GeneralLinearCuspidalMultiplicityOneStatement.md) | `47820896` | Getz–Hahn Theorem 11.4.3, Shalika 1974 Theorem 5.5: `Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearCuspidalMultiplicityOneStatement`. On the full almost-everywhere cuspidal subspace of `L²` for `GL_n` (`fullAEL2CuspidalSubmodule`), two irreducible closed invariant subspaces related by an equivariant isometric equivalence are equal. Strong multiplicity one (Getz–Hahn 11.7.2) is not stated here. |
| [ArthurCombinatoricsStatement](../../Langlands/LinearAlgebra/ArthurCombinatoricsStatement.md) with definitions [ArthurCombinatorics](../../Langlands/LinearAlgebra/ArthurCombinatorics.md) | `24a49431` | Arthur 1978 Proposition 1.1, the remark after Corollary 6.2 in relative form, Lemmas 6.1 and 6.3; Arthur 2005 (8.2) and Lemma 8.3: `Langlands.ArthurCombinatorics.ArthurCombinatoricsStatement`, for a finite crystallographic root system over `ℝ` with a Mathlib base. It is the abstract layer only. Reduced root systems only: a Mathlib base excludes type `BC`. The specialization to actual reductive groups belongs to the L3 foundations ([Arthur L3 foundations](arthur-l3-foundations-coverage.md)). |
| [CuspidalPairBoundaryNonvanishingStatement](../../Langlands/Global/Factors/CuspidalPairBoundaryNonvanishingStatement.md) | — | Shahidi 1981 Theorem 5.2: `Langlands.Global.CuspidalPairBoundaryNonvanishingStatement`. For actual cuspidal realizations of `GL_(r+1)` and `GL_(t+1)` with unitary central characters and a finite set `S` of finite places containing both exceptional sets, the partial L-function `L^S(s, π × π')` exists as a meromorphic function on `ℂ` given by the unramified Euler product on a right half-plane, and every such function has nonpositive `meromorphicOrderAt` (no zero) at each `1 + iy`. Holomorphy on `Re s = 1`, pole locations and boundedness in vertical strips are not stated. It is the global boundary nonvanishing input that `AppendixPoleCountingStatement.md` and `MeromorphicPoleComparisonStatement.md` assign to this program. |

The public support module
[AdelicMaximalCompactFactors](../../Langlands/Global/AdelicMaximalCompactFactors.md)
proves that a
maximal compact subgroup of `G(𝔸_F)` is the product of maximal compact
subgroups of `G(𝔸_{F,∞})` and `G(𝔸_{F,f})`, and conversely. It is a proof of
an internal lemma, not a source theorem.


| Exact target | Proof in the Library |
| --- | --- |
| `Langlands.Global.WhittakerExpansionStatement` | `whittakerExpansion` (`Langlands/Global/GeneralLinearWhittakerExpansionProof.lean`) |
| `Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearCuspidalMultiplicityOneStatement` | none recorded; conditional: `generalLinearCuspidalMultiplicityOne_of_summandEquivalence` (`Langlands/Automorphic/GeneralLinearCuspidalMultiplicityOneReduction.lean`) |
| `Langlands.ArthurCombinatorics.ArthurCombinatoricsStatement` (the six conjuncts as separate named theorems) | `arthurCombinatoricsStatement` (`Langlands/LinearAlgebra/ArthurCombinatoricsProof.lean`) |
| `Langlands.Global.CuspidalPairBoundaryNonvanishingStatement` | none recorded; conditional: from `CuspidalPairBoundaryNonvanishingEnlargedStatement` (`cuspidalPairBoundaryNonvanishingReduction`, `Langlands/Global/Factors/CuspidalPairBoundaryNonvanishingReduction.lean`), and from `CuspidalPairEisensteinCoefficientStatement` and `CuspidalPairEisensteinHolomorphyStatement` (`cuspidalPairEisensteinDerivation`, `Langlands/Global/Factors/CuspidalPairEisensteinDerivation.lean`) |

Shahidi's route to boundary nonvanishing uses the meromorphic continuation of Eisenstein
series, holomorphy on the imaginary axis and the `GL_n` Whittaker expansion, and feeds local
unitarity at Henniart's auxiliary places.

L4 targets with no statement in Library `ed924aef`, checked
by searching the Library's Markdown for their Getz–Hahn numbers (both are stated in the next
section):

- the pole part of Getz–Hahn Theorem 11.7.1, p.309, for cuspidal `π`, `π'`
  trivial on `A_GL`: simple poles only at `s = 0, 1`, present exactly when
  the ranks agree and `π' ≅ π^∨`, and boundedness in vertical strips. The published
  `CuspidalPairGlobalFunctionalEquationStatement` states the continuation
  and the functional equation only;
- Getz–Hahn Lemma 11.8.1, p.312. It assumes that `π_0, π_1, …, π_k` are
  cuspidal automorphic representations of `A_{GL_{n_i}} \ GL_{n_i}(𝔸_F)`,
  so each `π_i` is trivial on the split centre `A_{GL_{n_i}}` of its own
  group. Under that assumption the order of the pole at `s = 1` of
  `L(s, π_0 × ⊞_{i=1}^k π_i)` is the multiplicity of `π_0^∨` in
  `⊞_{i=1}^k π_i`, that is, the number of `i ≥ 1` with `π_i ≅ π_0^∨`. The
  split-centre assumption cannot be dropped: for `F = ℚ`, `π_0 = 1` and the
  single constituent `π_1 = |·|^{-1}` of `GL_1`, the L-function is
  `Λ_ℚ(s - 1)`, which has a simple pole at `s = 1`, although `π_1` is not
  `π_0^∨`.

Getz–Hahn Theorem 11.7.2 and Corollary 11.7.3 (strong multiplicity one,
cuspidal and isobaric, p.309) have numerical counterparts in the published
`CuspidalSpectralRigidityStatement` (Jacquet–Shalika II, Theorems 4.2 and
4.4; this note records no proof of it): its constituent recovery recovers lists of
full cuspidal classes from their Satake spectra outside a finite set, and its
singleton case recovers one class. Its Markdown records that it does not
compare local unramified components or construct actual isobaric
representations. The representation-theoretic forms of 11.7.2 and 11.7.3 were
not stated at this commit (see the section on strong multiplicity one below), and this ledger
does not duplicate the numerical ones.

Neither track of the program is complete.

## Getz–Hahn 11.7.1 poles, Lemma 11.8.1 and the H3 reduction

This section was checked on 13 November 2026 against Library
`46cfa5dd149a3809a3f9bf7a5de0d4f51ca2758c`. Both L4 targets listed at the end of the previous
section are stated here. The section also
records two H3 statements: the pole-comparison input and the reduction of
`CandidateExistenceStatement` to the open global inputs. The last column of the second table
gives their proofs.

| Module | First appeared at Library commit | Exact content and boundary |
| --- | --- | --- |
| [CuspidalPairPoleStatement](../../Langlands/Global/Factors/CuspidalPairPoleStatement.md) | `cfedefb6` | Getz–Hahn Theorem 11.7.1, pole part, p.309; Cogdell 2004 Theorems 4.1 and 4.2: `Langlands.Global.CuspidalPairPoleStatement`. For actual cuspidal realizations of `GL_(r+1)` and `GL_(t+1)` that are trivial on the split components `A_GL` of their centres, the finite local pair data and the archimedean standard-module parameters exist. Every completed pair L-function is holomorphic off `{0, 1}` and has at most simple poles at `0` and `1`. It has a pole there exactly when `r = t` and `T` realizes the contragredient of `T'`. It is bounded in vertical strips outside ε-discs about `0` and `1`. The functional equation is the separate published `CuspidalPairGlobalFunctionalEquationStatement`. |
| [CuspidalIsobaricPoleOrderStatement](../../Langlands/Global/Factors/CuspidalIsobaricPoleOrderStatement.md) | `cc5aa77f` | Getz–Hahn Lemma 11.8.1, p.312: `Langlands.Global.CuspidalIsobaricPoleOrderStatement`. Take cuspidal `T₀` and `T₁, …, T_k`, each trivial on the split component of its own centre. Then the data and the completed pair L-functions `Λ(s, π₀ × π_i)` exist, and `min(ord_{s=1} ∏ Λ(s, π₀ × π_i), 0) = -m`. Here `m` is the number of `i` with `T_i` realizing the contragredient of `T₀`. The isobaric sum itself is not constructed; the L-function of `π₀ × ⊞ π_i` is the product. The split-centre hypothesis is essential (counterexample in the previous section). |
| [RelativeCertifiedPoleComparisonsStatement](../../Langlands/Global/Factors/RelativeCertifiedPoleComparisonsStatement.md) | `730bd1f2` | Henniart 2000, Corollaire 2.4 and Lemme 2.8, pp.445–448, derived: `Langlands.Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement`. The published predicate `RelativeCertifiedPoleComparisons F E c v ψ` holds for all Galois extensions `E/F` of number fields, arithmetic fundamental class families `c`, finite places `v` and nontrivial additive characters `ψ` of `F_v`. That is, a `ψ`-self-dual measure exists. For every such measure the certified pair-factor data exist, with regular completed germs agreeing at `0` and both pole formulas. It is the universal form of the hypothesis of the proved `relativePolePairing`. It does not assert that any witnessed generator exists. |
| [HenniartCandidateExistenceReductionStatement](../../Langlands/Correspondence/HenniartCandidateExistenceReductionStatement.md) | `2e46b9ca` | Henniart 2000, §2.7, Théorème 3.1 and §§3.7–3.8, derived: `Langlands.Henniart.CandidateExistenceReductionStatement.{uK, uW, uP, uE, uQ}`. It is an implication with five hypotheses: Harris 1998 Proposition 4.8 (`Proposition48Statement.{uK, 0, 0, 0, uP}`), Henniart's Théorème 2.4 (`AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP}`), local relative class formation (`LocalRelativeClassFormationStatement.{0}`), the pole comparisons above (`.{0, uW, uP}`) and the composite-map statement (`HenniartCompositeMapStatement.{0, uK, uW, uP, uE}`). Its conclusion is `CandidateExistenceStatement.{uK, uW, 0, uE, uQ}`. The automorphic-lattice universe is `0` because the global construction produces number fields in `Type`. The transport to an arbitrary automorphic universe is not part of it. |


| Exact target and the inputs of its proof | Proof in the Library |
| --- | --- |
| `Langlands.Global.CuspidalPairPoleStatement`; Cogdell's route through the global Rankin–Selberg integrals and the mirabolic Eisenstein series | none recorded; conditional: `cuspidalPairPole_of_covering_normalized_products` (`Langlands/Global/Factors/CuspidalPairPoleEqualCover.lean`) |
| `Langlands.Global.CuspidalIsobaricPoleOrderStatement`; the pole statement above, Shahidi's nonvanishing (`CuspidalPairBoundaryNonvanishingStatement`), the symmetry of the contragredient relation and additivity of `meromorphicOrderAt` | none recorded; conditional: from `CuspidalPairPoleStatement` (`cuspidalIsobaricPoleOrderLandauReduction`, `Langlands/Global/Factors/CuspidalIsobaricPoleOrderLandauReduction.lean`) |
| `Langlands.Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement`; Henniart's Théorème 2.4 (`AssociatedSupercuspidalInductionStatement`) and Corollaire 2.4 (L, dual L and epsilon equalities at every finite place for weakly associate unitary pairs), the JPSS and Weil pole formulas, conjugacy of local maps and unitarity of central characters | none recorded |
| `Langlands.Henniart.CandidateExistenceReductionStatement`, from its five hypotheses and proved Library results only; it also required a Library repair, below | `candidateExistenceReduction` (`Langlands/Correspondence/HenniartCandidateExistenceReductionProof.lean`) |

The proof of the reduction required a repair. In Library `46cfa5dd` the theorem
`Langlands.Automorphic.OperatorRealization.evaluate_toContinuous_smul` was
declared twice, with the same statement, in
`Langlands/Automorphic/CuspidalAdmissible/Reproduction.lean` and in
`Langlands/Automorphic/OperatorScalarCentralCharacter.lean`. The reduction
needs `henniartGlobalization_of_inputs`, whose module imports the first,
together with `associatedCentralCharacter`, whose module imports the second,
so no module could use both. The repair moves the theorem to a new module,
`Langlands/Automorphic/OperatorRealizationEvaluation`, imported by both files; both former
copies are deleted. `Langlands.Henniart.candidateExistenceReduction` proves
`CandidateExistenceReductionStatement.{uK, uW, uP, uE, uQ}` (module
`Langlands/Correspondence/HenniartCandidateExistenceReductionProof`); it first appeared at
Library commit `457e31a2`. The reduction is conditional.

The inputs of the reduction and their status in the Library:

- Henniart's Théorème 2.4 (`AssociatedSupercuspidalInductionStatement`): this note records no
  proof;
- the pole comparisons (`RelativeCertifiedPoleComparisonsStatement`): this note records no
  proof;
- the composite-map statement (`HenniartCompositeMapStatement`), an assembly of four published
  statements (Henniart 3.8 for the composite map): this note records no proof;
- `LocalRelativeClassFormationStatement`: proved, as `localRelativeClassFormation`
  (`Langlands/ClassFieldTheory/Local/LocalRelativeClassFormationProof.lean`);
- Harris's Proposition 4.8 (`Proposition48Statement`): only the conditional
  `proposition48_of_hasSolution` is in the Library. The implication from Harris's
  Proposition 4.8 to `HenniartGlobalizationStatement` is
  `henniartGlobalization_of_inputs` (`Langlands/Global/Arithmetic/HenniartGlobalizationReduction.lean`);
  it does not prove the proposition.

GH's own proof of Lemma 11.8.1 ("apply Theorem 11.7.1") omits one input. A
zero at `s = 1` of some `Λ(s, π₀ × π_i)` with `π_i ≇ π₀^∨` would lower the
pole order. The statement Markdown (§6) supplies it from the published
Shahidi 1981 Theorem 5.2 (`CuspidalPairBoundaryNonvanishingStatement`).

Further L4 targets of the program's list. A search of the Library's
Markdown for their Getz–Hahn numbers, and of its Lean for the half-plane
condition `1 ≤ s.re`, found no statement at this commit of (the next sections state them):

- the representation-theoretic forms of Getz–Hahn Theorem 10.7.2
  (Jacquet–Shalika 1981, Theorem 4.4), p.287, and of Theorem 11.7.2 and
  Corollary 11.7.3, p.309. Their numerical counterparts are in the published
  `CuspidalSpectralRigidityStatement` (previous section);
- the isobaric representations of Getz–Hahn Theorem 10.7.5 and
  Definition 10.7.6, pp.288–289. `PositiveRankCuspidalClass` carries
  mixed-rank lists of cuspidal classes, but no isobaric sum is constructed;
- Getz–Hahn Theorem 11.5.2, p.305: for unitary `π`, `π'` the local
  `L(s, π × π')` is holomorphic and nonzero for `Re s ≥ 1`. The Library
  states only special cases: Jacquet–Shalika's convergence of the
  equal-rank integrals of unitary generic pairs on `Re s ≥ 1`
  (`EqualRankEulerStatement`) and the unramified case
  (`UnramifiedUnitaryPoleFreeStatement`, proved as
  `unramifiedUnitaryPoleFree`). GH's archimedean reference, Barthel–
  Ramakrishnan 1994, §2, is recorded by the roadmap as missing.

H3 is reduced, by the proved reduction, to the five inputs above, of which the Library proves
`LocalRelativeClassFormationStatement`. Neither track of the program is complete.

## Strong multiplicity one, local regularity, inducing-data rigidity, isobaric sums and constituents of induced representations

This section was checked on 14 November 2026 against Library
`39ad1eee1f5962f7803f7298b1798932d7f29192`; its Lean files are
those of Library `757a6793`. Of the L4 targets listed at the end of the previous section, these
are stated here: the representation-theoretic forms
of GH Theorems 10.7.2 and 11.7.2, GH Theorem 10.7.5 at the finite places, and
the p-adic case of GH Theorem 11.5.2. These were not stated at this commit: the
representation-theoretic form of GH Corollary 11.7.3 (strong multiplicity one
for isobaric representations), GH Definition 10.7.6, GH Theorem 10.7.5 at the
infinite places, and the archimedean case of GH Theorem 11.5.2 (see the end of
this section). The last column of the second table gives their proofs.

| Module | First appeared at Library commit | Exact content and boundary |
| --- | --- | --- |
| [CuspidalStrongMultiplicityOneStatement](../../Langlands/Global/Factors/CuspidalStrongMultiplicityOneStatement.md) | `430cc03f` | Getz–Hahn Theorem 11.7.2, p.309; Jacquet–Shalika 1981 I, Theorem 4.8 and Corollary 4.10: `Langlands.Global.CuspidalStrongMultiplicityOneStatement.{u, uQ}`. Take cuspidal realizations `T`, `T'` of `GL_(r+1)` with spectral presentations whose finite local components are irreducible and admissible. If their finite local classes agree outside a finite set of finite places, then `T.isoClass = T'.isoClass`. Nothing is assumed at the infinite places. The numerical forms (equal Satake spectra) are the singleton cases of `CuspidalSpectralRigidityStatement`. |
| [UnitaryGenericLPolynomialNonvanishingStatement](../../Langlands/Representation/RankinSelberg/UnitaryGenericLPolynomialNonvanishingStatement.md) | `430cc03f` | Getz–Hahn Theorem 11.5.2, p.305, p-adic case: `Langlands.RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement.{uF, uV, uW}`. For generic (`Whittaker.IsGeneric`) unitarizable representations `π`, `σ` of `GL_(r+1)` and `GL_(t+1)` over a p-adic field, every symmetric L-polynomial `P` of the pair (`IsPadicSymmetricLPolynomial`) satisfies `P(q^(-s)) ≠ 0` for `Re s ≥ 1`, so `L(s, π × σ) = 1/P(q^(-s))` is holomorphic there. The archimedean case (GH cite Barthel–Ramakrishnan 1994, §2) is not stated. |
| [CuspidalInducingDataRigidityStatement](../../Langlands/Global/Factors/CuspidalInducingDataRigidityStatement.md) | `c257f7cc` | Getz–Hahn Theorem 10.7.2, p.287; Jacquet–Shalika 1981 II, Theorem 4.4, p.809: `Langlands.Global.CuspidalInducingDataRigidityStatement.{u, uQ}`. Take two families of cuspidal realizations `T i` of `GL_(m i + 1)` and `T' j` of `GL_(m' j + 1)` with `∑ (m i + 1) = ∑ (m' j + 1) = r + 1`, and presentations irreducible and admissible at every finite place. Suppose that at every finite place outside a finite set the local components are spherical and the two normalized block inductions have a common spherical subquotient. Then a bijection `e` of the index sets matches the full cuspidal classes, with multiplicity. Nothing is assumed at the infinite places. |
| [IsobaricSum](../../Langlands/Representation/Classification/IsobaricSum.md) and [CuspidalIsobaricRealizationStatement](../../Langlands/Global/Factors/CuspidalIsobaricRealizationStatement.md) | `757a6793` | Getz–Hahn Theorem 10.7.5, p.288, at the finite places. `PadicField.TopologicalData.IsIsobaricSum` is the local isobaric sum `π_1 ⊞ ⋯ ⊞ π_k` over a p-adic field, through the Langlands heads of multisegments (Kudla 1994, Theorem 1.2.5). `Langlands.Global.CuspidalIsobaricRealizationStatement.{u, uQ}`: for cuspidal realizations `T i` of `GL_(m i + 1)` with presentations irreducible and admissible at every finite place, there is an irreducible operator subquotient `Q` of rank `r + 1` such that at every finite place `v` the isobaric sum of the `σ_(i,v)` exists, is a subquotient of the normalized block induction, and embeds in the restriction of `Q` to `GL_(r+1)(F_v)`. Not stated: the infinite places, `Q` as a subquotient of the global induced representation, uniqueness, and GH Definition 10.7.6 (a predicate read only at finite places would be too weak; see the statement Markdown, §6). |
| [CuspidalInducedConstituentAutomorphyStatement](../../Langlands/Global/Factors/CuspidalInducedConstituentAutomorphyStatement.md) | `757a6793` | Getz–Hahn Theorem 10.7.1, first half, pp.286–287; Langlands 1979, Lemma 1 and Proposition 2, pp.203–204 (Getz–Hahn's "appendix to [BJ79]"), at the finite places: `Langlands.Global.CuspidalInducedConstituentAutomorphyStatement.{u, uQ}`. Take cuspidal realizations `T i` of `GL_(m i + 1)` with `∑ (m i + 1) = r + 1` and presentations irreducible and admissible at every finite place. For every finite place `v` let `A v` be an object of the canonical category of `GL_(r+1)(F_v)` that is a subquotient (`IsSubquotientOf`) of the normalized block induction of the `σ_(i,v)`, with a nonzero `GL_(r+1)(O_v)`-fixed vector for `v` outside a finite set. Then one irreducible operator subquotient `Q` of rank `r + 1` receives an injective intertwiner from `A v` into its restriction to `GL_(r+1)(F_v)`, for every finite `v`. Not stated: the infinite places, the converse half of 10.7.1 (every automorphic representation is such a constituent), and `Q` as a constituent of the global induced representation. The isobaric statement above is this statement applied to the local isobaric sums. |

The numerical rigidity that the proofs of the first and third statements need is
the published `CuspidalSpectralRigidityStatement`
(`Langlands/Automorphic/Unramified/CuspidalSpectralRigidityStatement.lean`,
first appeared at Library `0123ad79`): Jacquet–Shalika 1981 II, Theorem 4.2 (power-trace
independence of distinct cuspidal classes) and the numerical step of
Theorem 4.4 (recovery of the constituents, with multiplicity, from trace sums
or Euler products). Its route is in the table below.


| Exact target and the inputs of its proof | Proof in the Library |
| --- | --- |
| `UnitaryGenericLPolynomialNonvanishingStatement`; GH's deduction from Proposition 11.5.1: absolute convergence and holomorphy on `Re s ≥ 1` of the local Rankin–Selberg integrals (in equal rank `UnitaryEqualRankConvergenceStatement`, since proved as `unitaryEqualRankConvergence`), then the proved regularity results for rational continuations and normalized generators | `unitaryGenericLPolynomialNonvanishing` (`Langlands/Representation/RankinSelberg/UnitaryGenericLPolynomialNonvanishingProof.lean`) |
| `CuspidalStrongMultiplicityOneStatement`; GH's route through the pole of `Λ(s, π × π'^∨)` (`CuspidalPairPoleStatement`), regularity of the exceptional local factors (`UnitaryGenericLPolynomialNonvanishingStatement` at finite places; the archimedean case of GH 11.5.2 was missing from the Library at this commit) and a common determinant twist | none recorded; conditional: `cuspidalStrongMultiplicityOne_of_nondualPartialEulerContinuation` (`Langlands/Global/Factors/CuspidalStrongMultiplicityOnePoleReduction.lean`) |
| `CuspidalSpectralRigidityStatement`; Jacquet–Shalika 1981 II, Theorems 4.1 and 4.2 and the proof of 4.4: absolute convergence for `Re s > 1` (JS I, Lemma 5.2 and Theorem 5.3; not in the Library at this commit), the pole at `s = 1` (`CuspidalPairPoleStatement` with `UnitaryGenericLPolynomialNonvanishingStatement`, or JS II Proposition 3.6), Shahidi's nonvanishing on `Re s = 1` (`CuspidalPairBoundaryNonvanishingStatement`), unitary twists, and the proved `eulerProductTrace` | none recorded; conditional: from `CuspidalPairPoleStatement` (`cuspidalSpectralRigidityLandauReduction`, `Langlands/Automorphic/Unramified/CuspidalSpectralRigidityLandauReduction.lean`, with the proved `cuspidalPairAbsoluteConvergence`) and from `CuspidalPowerTraceIndependenceStatement` (`cuspidalSpectralRigidity_of_independence`) |
| `CuspidalInducingDataRigidityStatement`; the Satake class of a block induction as the concatenation of the blocks' classes (spherical constituent existence and uniqueness, induction in stages), comparison with the presentations' spectral systems, then the recovery conjunct of `CuspidalSpectralRigidityStatement` | none recorded; conditional: from `CuspidalEulerConstituentRecoveryStatement` (`cuspidalInducingDataRigidity_of_constituentRecovery`, `Langlands/Global/Factors/CuspidalInducingDataRigidityReduction.lean`) |
| `CuspidalInducedConstituentAutomorphyStatement`; Langlands' proof of Proposition 2, pp.205–207: Eisenstein series near a point of the parameter space, their derivatives, Lemmas 7–9 through constant terms along associate parabolics, and Jordan–Hölder. Its analytic input is the Library's general-reductive Eisenstein statements (`Langlands/Global/AdelicEisenstein*`: absolute convergence and meromorphic continuation of Eisenstein series and of intertwining operators; see the Bernstein–Lapid sections above for their proofs). Then the easy direction of Lemma 1, a choice of archimedean constituents, and the tensor embedding into an `IrreducibleOperatorSubquotient` | none recorded |
| `CuspidalIsobaricRealizationStatement`; local isobaric sums from the proved `multisegmentHeadExhaustion` and `multisegmentHeadExistence`; the isobaric sum as a subquotient of the block induction by induction on the number of blocks from the proved `langlandsHeadProductSubquotient` (Tadić 1986, Proposition A.4(ii)) and induction in stages; sphericity almost everywhere (Getz–Hahn Theorem 10.6.3) through the proved `orderedUnramifiedSphericalGeneration`; then `CuspidalInducedConstituentAutomorphyStatement`. The local steps do not depend on it | none recorded; conditional: from `CuspidalInducedConstituentAutomorphyStatement` (`cuspidalIsobaricRealizationReduction`, `Langlands/Global/Factors/CuspidalIsobaricRealizationReduction.lean`) |


H3 inputs. Of the five hypotheses of `CandidateExistenceReductionStatement` (previous
section), `LocalRelativeClassFormationStatement` is proved by projection from the proved
`localAbsoluteCorestrictionCompatibleClassFormation`; the Library's proof is
`localRelativeClassFormation`. Harris 1998 Proposition 4.8 (`Proposition48Statement`) is a
separate deep prerequisite, outside this program; the reduction uses it at universes
`{uK, 0, 0, 0, uP}`.

Further L4 targets. Missing from the Library at this commit (later sections state some of
them):

- the archimedean case of Getz–Hahn Theorem 11.5.2;
- Jacquet–Shalika's absolute convergence of partial Rankin–Selberg
  L-functions for `Re s > 1` (JS I, Theorem 5.3);
- the converse half of GH Theorem 10.7.1 (every automorphic representation is
  a constituent of an induced representation);
- GH Corollary 10.7.3, p.287: an irreducible subquotient of two cuspidally
  induced representations determines the cuspidal data up to permutation. It
  needs the global induced representation, which is not in the Library;
- GH Definition 10.7.6, pp.288–289, and GH Theorem 10.7.5 at the infinite
  places;
- the representation-theoretic form of GH Corollary 11.7.3, p.309 (if two
  isobaric automorphic representations of `GL_n(A_F)` have isomorphic
  components outside a finite set of places, they are isomorphic). Its
  numerical counterpart, the recovery of the cuspidal constituents with
  multiplicity from Euler products, is the published
  `CuspidalSpectralRigidityStatement`. Neither the cuspidal
  `CuspidalStrongMultiplicityOneStatement` nor the finite-place
  `CuspidalIsobaricRealizationStatement` compares two global isobaric
  representations. The corollary first needs the global isobaric interface of
  GH Definition 10.7.6.

Neither track of the program is complete.

## Isobaric automorphic representations at every place

This section was checked on 14 November 2026 against Library
`4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2`. Of the L4 targets listed at the end of the
previous section, these are stated here: GH Definition 10.7.6, GH
Theorem 10.7.5 at every place (including the real and complex places), and the
representation-theoretic form of GH Corollary 11.7.3. These were not stated at this commit:
the archimedean case of GH Theorem 11.5.2, JS I Theorem 5.3, the converse half
of GH Theorem 10.7.1, and GH Corollary 10.7.3. The second table gives the proofs of the two
statements.

| Module | First appeared at Library commit | Exact content and boundary |
| --- | --- | --- |
| [IsobaricAutomorphicRepresentation](../../Langlands/Global/Factors/IsobaricAutomorphicRepresentation.md) | `4f6abf4c` | Getz–Hahn Definition 10.7.6, pp.288–289, with (10.30), p.283, and (10.35), p.288; seven definitions, no theorems. `RealBlock.exponent`, `IsRealLanglandsOrdered` and `IsComplexLanglandsOrdered` order archimedean blocks by weakly decreasing real part of the exponent (GH (10.30)). `OperatorSubquotient.HasRealPlaceLanglandsQuotient v ds` (and the complex analogue) says that the list is in that order and that some `(𝔤_v, K_v)`-map from `realStandardKFinite` of `ds` into the subquotient has nonzero image, irreducible under the compact and Lie actions at `v`. `IrreducibleOperatorSubquotient.IsCuspidalIsobaricSum Q T P h` says: at every finite place `Q` receives an injective intertwiner from an object `A` with `IsIsobaricSum (σ_(i,v)) A`; at every real (complex) place there are parameters `ds i` of the realizations `T i` and a reordering `ds'` of their concatenation with `HasRealPlaceLanglandsQuotient v ds'` (complex analogue). `IsIsobaric Q` is the existence of such cuspidal data. Not asserted: existence or uniqueness of the local data, admissibility of `Q`, invariance under equivalence or change of presentation, and GH's description through the global induced representation. |
| [CuspidalIsobaricAutomorphyStatement](../../Langlands/Global/Factors/CuspidalIsobaricAutomorphyStatement.md) | `4f6abf4c` | Getz–Hahn Theorem 10.7.5, p.288, at every place: `Langlands.Global.CuspidalIsobaricAutomorphyStatement.{u, uQ}`. For cuspidal realizations `T i` of `GL_(m i + 1)` with `∑ (m i + 1) = r + 1` and presentations irreducible and admissible at every finite place, there is `Q : IrreducibleOperatorSubquotient F r` with `Q.IsCuspidalIsobaricSum T P h`. It strengthens the finite-place `CuspidalIsobaricRealizationStatement` at the infinite places but omits that statement's condition that `A` is a subquotient of the local induced representation. Not asserted: `Q` as a subquotient of the global induced representation, and uniqueness. With `k = 1` it implies `CuspidalArchimedeanParameterExistenceStatement`. |
| [IsobaricStrongMultiplicityOneStatement](../../Langlands/Global/Factors/IsobaricStrongMultiplicityOneStatement.md) | `4f6abf4c` | Getz–Hahn Corollary 11.7.3, p.309 (left as Exercise 11.8): `Langlands.Global.IsobaricStrongMultiplicityOneStatement.{u, uQ}`. For `Q Q' : IrreducibleOperatorSubquotient F r` with `IsIsobaric Q` and `IsIsobaric Q'`, and a finite set `S` of finite places such that at every finite `v ∉ S` one object `A` embeds injectively in both restrictions to `GL_(r+1)(F_v)`, there is a `Q.Equivalence Q'` (finite adelic translations, compact actions and enveloping-algebra actions). The hypothesis says nothing at the infinite places. Not asserted: equality as subquotients, multiplicity one in the space of automorphic forms. |


| Exact target and the inputs of its proof | Proof in the Library |
| --- | --- |
| `CuspidalIsobaricAutomorphyStatement`; the finite places as for `CuspidalIsobaricRealizationStatement`; the archimedean parameters through `CuspidalArchimedeanParameterExistenceStatement` (proved, as `cuspidalArchimedeanParameterExistence`) and `RealLanglandsQuotientStatement` (proved, as `realLanglandsQuotient`); the archimedean case of GH Theorem 10.6.4 (Knapp 1994, Theorems 1 and 4); and an all-places form of GH Theorem 10.7.1 with prescribed archimedean constituents, which is not in the Library (the public `CuspidalInducedConstituentAutomorphyStatement` controls only the finite places) and must be stated and proved separately | none recorded; conditional: `cuspidalIsobaricAutomorphy_of_tensorRealization` (`Langlands/Global/Factors/CuspidalIsobaricTensorRealization.lean`) |
| `IsobaricStrongMultiplicityOneStatement`; admissibility of irreducible automorphic subquotients (Borel–Jacquet 1979, Proposition 4.5 and §4.6, p.196) and Flath's factorization including the archimedean `(𝔤, K)`-modules (Flath 1979, Theorem 3, p.181), neither in the Library; `CuspidalInducingDataRigidityStatement` through its proof; independence of the local components from the presentation (not in the Library); uniqueness of local isobaric sums (Kudla Theorem 1.2.5) and of Langlands quotients (Knapp Theorem 1(c), Theorem 4) | none recorded; conditional: from `CuspidalInducingDataRigidityStatement` and the proved `RealStandardIsotypicParameterUniquenessStatement` (`isobaricStrongMultiplicityOne_of_rigidity_and_real_parameters`, `Langlands/Global/Factors/IsobaricStrongMultiplicityOneReduction.lean`) |

Further L4 targets. Missing from the Library at this commit (later sections state some of
them):

- the archimedean case of Getz–Hahn Theorem 11.5.2;
- Jacquet–Shalika's absolute convergence of partial Rankin–Selberg
  L-functions for `Re s > 1` (JS I, Theorem 5.3);
- the converse half of GH Theorem 10.7.1 (every automorphic representation is
  a constituent of an induced representation);
- GH Corollary 10.7.3, p.287, which needs the global induced representation;
- GH Theorem 10.7.1 at every place: the finite-place statement with prescribed
  constituents at the real and complex places (Langlands 1979, Lemma 1 and
  Proposition 2, pp.203–204);
- admissibility of irreducible operator subquotients (Borel–Jacquet 1979,
  Proposition 4.5 and §4.6, p.196);
- Flath's factorization of irreducible admissible representations of
  `GL_n(𝔸_F)` with the archimedean `(𝔤, K)`-modules (Flath 1979, Theorem 3,
  p.181); the Library has it for the finite adelic group only
  (`flathRestrictedProductExistence`);
- independence of the finite local components of a cuspidal realization from
  its spectral presentation.

The last four are prerequisites of the proofs of `CuspidalIsobaricAutomorphyStatement` and
`IsobaricStrongMultiplicityOneStatement`. Neither track of the program is complete.

## Admissibility of automorphic representations

This section was checked on 14 November 2026 against Library
`c40a01345b2f4172fa41e07ff31644b40e695003`. Of the L4 targets listed at the end of the previous
section, admissibility
of irreducible operator subquotients (Borel–Jacquet 1979, Proposition 4.5 and
§4.6, p.196) is stated here, together with Harish-Chandra's
finiteness theorem in the form of Borel–Jacquet §4.3 (i), p.195. Both are
in one module of definitions and statements; the second table gives the proofs of its three
statements. Page numbers are printed pages of the registered
Corvallis Part I file `borel-jacquet-1979-automorphic` (printed page = PDF
page + 5).

| Module or statement | Exact content and boundary |
| --- | --- |
| [AutomorphicAdmissibilityStatement](../../Langlands/Automorphic/AutomorphicAdmissibilityStatement.md), definitions | Three definitions for `GL_n` over a number field `F`. `centerAnnihilatedForms F n J` is the space of automorphic forms killed by every element of an ideal `J` of `ArchimedeanGL.EnvelopingCenter F n` through `automorphicEnvelopingAction`. `annihilatedFormMultiplicitySpace F n J L σ` is the space of linear maps `φ : (Fin m → ℂ) →ₗ[ℂ] AutomorphicForms F n` that intertwine `σ` with `automorphicCompactRightAction` and take values in the forms fixed by `L` under `automorphicFiniteRightAction` (`jointMultiplicitySpace`) and in `centerAnnihilatedForms F n J`. `OperatorSubquotient.IsJointlyAdmissible Q` is `Langlands.IsJointlyAdmissible Q.finiteRepresentation Q.compactRepresentation`: for every open subgroup `L` of `GL_n(𝔸_f)` and every representation `σ` of `standardInfiniteCompact F n` on `Fin m → ℂ`, the joint multiplicity space of the quotient is finite-dimensional. |
| `HarishChandraFinitenessStatement` (same files) | Borel–Jacquet §4.3 (i), p.195, derived there from Harish-Chandra's Theorem 1.7, p.191: `Langlands.Automorphic.HarishChandraFinitenessStatement.{u}`. For every ideal `J` of finite codimension in the center (`Module.Finite ℂ (EnvelopingCenter F n ⧸ J)`), every `L : OpenSubgroup (FiniteAdelicGL F n)` and every `σ` as above, `annihilatedFormMultiplicitySpace F n J L σ` is finite-dimensional. Admissibility is in the Library's Hom form (all finite-dimensional `σ`, all open `L`) instead of Borel–Jacquet's simple idempotents. Not asserted: §4.3 (ii)–(iv), §4.4, anything about square-integrable forms, or groups other than `GL_n`. |
| `GeneratedFormAdmissibilityStatement` (same files) | Borel–Jacquet Proposition 4.5, (1) ⇒ (4), p.196: `Langlands.Automorphic.GeneratedFormAdmissibilityStatement.{u}`. For every automorphic form `f`, `generatedFormOperatorRealization F n f` (the Library's form of `f * ℋ`) satisfies `OperatorRealization.IsJointlyAdmissible`. Not asserted: the converse implications (4) ⇒ (3) ⇒ (2) ⇒ (1), or conditions (2) and (3) at single places. |
| `IrreducibleSubquotientAdmissibilityStatement` (same files) | The admissibility claim of Borel–Jacquet §4.6, p.196: `Langlands.Automorphic.IrreducibleSubquotientAdmissibilityStatement.{u}`. Every `Q : OperatorSubquotient F n` with `Q.IsIrreducible` satisfies `Q.IsJointlyAdmissible`. Neither cuspidality nor a central character is assumed. Not asserted: any factorization of `Q` into local components, or the comparison of a realization `S` with the subquotient `S/⊥`. |

Relation to earlier Library results. Before this module the Library had joint
admissibility only for cuspidal realizations with unitary central character
(`cuspidalUnitaryContragredientExistence`, through
`CuspidalAdmissible.isJointlyAdmissible_of_siegelFiniteness` and the proved
`siegelSetGLFiniteness`), and the one-function archimedean finiteness of
Borel–Jacquet Lemma 2.1, p.193
(`ArchimedeanGL.generatedCompactTypeFiniteness`, proved). Neither gives
`HarishChandraFinitenessStatement`, which bounds all automorphic forms of a
given type at once.


| Exact target and the inputs of its proof | Proof in the Library |
| --- | --- |
| `HarishChandraFinitenessStatement`; route of Borel–Jacquet §4.3: reduction to compact open `L` and to finitely many continuous irreducible `K_∞`-types, finiteness of `GL_n(F)\GL_n(𝔸)/G_∞ L` (§4.3 (2)), and Harish-Chandra's finiteness on `G_∞` for the arithmetic subgroups `Γ_c` (Theorem 1.7, p.191; Harish-Chandra 1968, Chapter I, §2, Theorem 1, p.8, proved in §6). The Library has the cuspidal part of the argument (`CuspidalAdmissible/Reproduction.lean`, `Finiteness.lean`, `JointAdmissibility.lean`) and constant terms (`ConstantTerm.lean`, `GeneralLinearIntrinsicConstantTerm.lean`); the bounds for non-cuspidal forms through their constant terms were not in the Library at this commit | `harishChandraFiniteness` (`Langlands/Automorphic/HarishChandraFinitenessProof.lean`) |
| `GeneratedFormAdmissibilityStatement` through a proof of `HarishChandraFinitenessStatement`; the ideal `J` of finite codimension killing `f` (`isCenterFinite_iff_exists_ideal`), and the fact that `J` kills the whole generated realization, which needs the invariance of the center of the enveloping algebra under `Ad(K_∞)` compatibly with the Library's actions (this compatibility may need to be proved) | `generatedFormAdmissibility` (`Langlands/Automorphic/GeneratedFormAdmissibilityProof.lean`) |
| `IrreducibleSubquotientAdmissibilityStatement` through a proof of `GeneratedFormAdmissibilityStatement`; a cyclic vector `f ∈ Q.upper \ Q.lower` whose generated realization maps onto `Q.Space`; joint admissibility of quotients (averaging over compact open `L`, isotypic projections for `K_∞`); and possibly a lemma comparing `OperatorRealization.IsJointlyAdmissible` with the subquotient form | `irreducibleSubquotientAdmissibility` (`Langlands/Automorphic/IrreducibleSubquotientAdmissibilityProof.lean`) |

The proof of `IsobaricStrongMultiplicityOneStatement` uses admissibility of irreducible
operator subquotients in its first step.

Further L4 targets. Of the list at the end of the previous section, the
admissibility of irreducible operator subquotients is stated here. Missing from the Library as
statements at this commit (later sections state some of them):

- the archimedean case of Getz–Hahn Theorem 11.5.2;
- Jacquet–Shalika's absolute convergence of partial Rankin–Selberg
  L-functions for `Re s > 1` (JS I, Theorem 5.3);
- the converse half of GH Theorem 10.7.1;
- GH Corollary 10.7.3, p.287;
- GH Theorem 10.7.1 at every place (Langlands 1979, Lemma 1 and
  Proposition 2, pp.203–204);
- Flath's factorization of irreducible admissible representations of
  `GL_n(𝔸_F)` with the archimedean `(𝔤, K)`-modules (Flath 1979, Theorem 3,
  p.181);
- independence of the finite local components of a cuspidal realization from
  its spectral presentation.

Of the target statements of this section and the previous two, the Library proves
`HarishChandraFinitenessStatement` (`harishChandraFiniteness`),
`GeneratedFormAdmissibilityStatement` (`generatedFormAdmissibility`),
`IrreducibleSubquotientAdmissibilityStatement` (`irreducibleSubquotientAdmissibility`) and
`UnitaryGenericLPolynomialNonvanishingStatement` (`unitaryGenericLPolynomialNonvanishing`). It
has conditional proofs of `CuspidalIsobaricAutomorphyStatement`
(`cuspidalIsobaricAutomorphy_of_tensorRealization`) and `CuspidalStrongMultiplicityOneStatement`
(`cuspidalStrongMultiplicityOne_of_nondualPartialEulerContinuation`). This note records no proof
of `IsobaricStrongMultiplicityOneStatement`, `CuspidalSpectralRigidityStatement`,
`CuspidalInducingDataRigidityStatement`, `CuspidalInducedConstituentAutomorphyStatement` or
`CuspidalIsobaricRealizationStatement`. As the Library is now, all of these except
`CuspidalInducedConstituentAutomorphyStatement` have conditional proofs, named in the tables
above; none of the five is proved outright. Neither track of the program is complete.

## Local components, absolute convergence, archimedean Theorem 11.5.2, cuspidal support

This section was checked on 14 November 2026 against Library
`4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86`. It records
four modules of definitions and statements. Four items of the list of L4 targets at the end of
the previous section are stated here: the archimedean case of
Getz–Hahn Theorem 11.5.2, Jacquet–Shalika I Theorem (5.3), and the converse
half of GH Theorem 10.7.1 and GH Corollary 10.7.3, the last two read at the
finite places only. The fourth module states the existence and uniqueness of
the local components of GH Theorem 6.3.7, read through isotypic restriction
at each place; it does not state Flath's tensor factorization. The second table gives the
proofs of the statements of the four modules. Page numbers are printed pages; each
module's Markdown gives the PDF pages of the registered files.

| Module | Exact content and boundary |
| --- | --- |
| [OperatorSubquotientLocalComponentStatement](../../Langlands/Automorphic/OperatorSubquotientLocalComponentStatement.md) | Five definitions and three statements for `Q : IrreducibleOperatorSubquotient F r` over a number field `F`, each statement assuming `Q.subquotient.IsJointlyAdmissible`. `Archimedean.gkHoms` is the space of `(𝔤, K)`-module maps and `Archimedean.IsGKIsotypic` says that their ranges span the target. `OperatorSubquotient.IsFinitePlaceIsotypic Q v ρ` says that the ranges of the intertwining maps from `ρ` to `Q.localRepresentation v` span `Q.Space`; `IsRealPlaceIsotypic` and `IsComplexPlaceIsotypic` say the same for the `O(r+1)` or `U(r+1)` translation and the Lie action at one infinite place. `LocalComponentExistenceStatement.{u}` (GH Theorem 6.3.7, p.165, existence of the factors; Flath 1979, Theorem 3, p.181): at every finite place some `A : AutomorphicObject.{u, u} (padicField v) r.succPNat` makes `Q` isotypic, and at every real or complex place some irreducible admissible module satisfying `IsRealGKModule` or `IsComplexGKModule`, on a carrier in `ModuleCat.{u} ℂ`, makes `Q` isotypic. `LocalComponentEmbeddingStatement.{u, uW}` (derived; Flath, p.180): an irreducible local representation makes `Q` isotypic exactly when it has a nonzero intertwining map into the restriction of `Q`. `LocalComponentDeterminationStatement.{u}` (GH Theorem 6.3.7 with the uniqueness of the factors; Flath Theorem 3): `Nonempty (Q.Equivalence Q')` holds exactly when at every place one irreducible local representation makes both `Q` and `Q'` isotypic. Not asserted (Markdown §8): a tensor product isomorphism `Q ≅ ⊗_v π_v` or an `OperatorQuotientTensorPresentation` of `Q`; that almost all components are unramified; genericity or unitarity of the components of cuspidal representations. |
| [CuspidalPairAbsoluteConvergenceStatement](../../Langlands/Global/Factors/CuspidalPairAbsoluteConvergenceStatement.md) | One definition and three statements for actual cuspidal realizations with spectral presentations `P`, `P'` and a finite set `S` of finite places containing both exceptional sets. `CuspidalPairAbsoluteConvergence.logEulerTerm P P' hP hP' v n s` is `tr(A_v^k) tr(A'_v^k) q_v^(-ks) / k` with `k = n + 1`. `CuspidalSelfPairContinuationStatement.{u, uQ}` (JS I Lemma (5.2), pp.554–555): if `T` has `HasUnitaryCentralCharacter` and `Td` realizes its contragredient, some `L : ℂ → ℂ` is complex differentiable on `Re s > 1` and, on some right half-plane, is the value of the absolutely convergent product of `partialEulerFactor P Pd hP hPd v s` over `v ∉ S`. `CuspidalPairAbsoluteConvergenceStatement.{u, uQ}` (the entry; JS I Theorem (5.3), p.555, with the double series of its proof, pp.555–557): if `T` and `T'` have unitary central characters and `1 < Re s`, the double series of `‖logEulerTerm P P' hP hP' v n s‖` over `(v, n)` is summable, `∑_(v ∉ S) ‖partialEulerFactor P P' hP hP' v s − 1‖` converges, and the product over `v ∉ S` has value `exp` of the sum of the double series. `CuspidalPairAbsoluteConvergenceReductionStatement.{u, uQ}` is the implication from Lemma (5.2) to Theorem (5.3). Not asserted (Markdown §5): anything on the line `Re s = 1`, meromorphic continuation, poles or growth; holomorphy of `L^S` on `Re s > 1` is not stated separately. |
| [UnitaryGenericPairRegularityStatement](../../Langlands/Representation/Archimedean/UnitaryGenericPairRegularityStatement.md) | Two predicates and eight statements in namespace `Langlands.Archimedean`. `IsRealUnitarizableGKModule n ρ π` and `IsComplexUnitarizableGKModule n ρ π` ask for a `K`-invariant positive definite Hermitian form (`InvariantPositiveForm ρ`) for which every `X ∈ 𝔤₀` acts by a skew-Hermitian operator (Knapp–Vogan 1995, (0.5), p.6). `RealUnitaryGenericExponentBoundStatement.{uV}` and `ComplexUnitaryGenericExponentBoundStatement.{uV}`: an irreducible admissible generic unitarizable `(𝔤, K)`-module with standard parameter `ds` has `\|realBlockExponent x\| < 1/2` (complex: `\|x.exponent.re\| < 1/2`) for every block `x ∈ ds`. `RealPairLFactorRightHalfPlaneRegularityStatement` and `ComplexPairLFactorRightHalfPlaneRegularityStatement`: if `0 < Re s + realBlockExponent x + realBlockExponent y` for all `x ∈ ds`, `y ∈ ds'` (complex: with `x.exponent.re + y.exponent.re`), the denominator of the pair `L`-factor does not vanish at `s`. `RealUnitaryGenericPairRegularityStatement.{uV, uW}` and `ComplexUnitaryGenericPairRegularityStatement.{uV, uW}` (the entries; GH Theorem 11.5.2, p.305, archimedean case): for two such modules with standard parameters `ds`, `ds'`, `(realPairLFactor ds ds').denominator s ≠ 0` (complex: `complexPairLFactor`) whenever `1 ≤ Re s`. The two reduction statements say that the bounds at `uV` and `uW` and the regularity imply the entry. Not asserted (Markdown, "Correspondence with Getz–Hahn" and "Relation to published statements"): anything for `Re s < 1`; the existence of standard parameters, which are hypotheses; that the archimedean components of unitary cuspidal automorphic representations satisfy the hypotheses. |
| [CuspidalSupportStatement](../../Langlands/Global/Factors/CuspidalSupportStatement.md) | One predicate and two statements. `IsFiniteInducedConstituent hm P h Q` asks for `A v : AutomorphicObject.{u, u} (padicField v) r.succPNat` at every finite place and a finite set `S` of finite places such that, at every finite place, `A v` is a subquotient of the normalized induction of the canonical local components of the cuspidal data, `A v` has a nonzero `GL_(r+1)(O_v)`-fixed vector when `v ∉ S`, and `A v` embeds injectively into `Q.subquotient.localRepresentation v`. `CuspidalSupportExistenceStatement.{u}` (the converse half of GH Theorem 10.7.1, pp.286–287; Langlands 1979, Proposition 2, "only if", p.204): every `Q : IrreducibleOperatorSubquotient F r` satisfies the predicate for some cuspidal data with presentations in universe `u`. `CuspidalSupportUniquenessStatement.{u, uQ}` (GH Corollary 10.7.3, p.287): two families of cuspidal data for which the predicate holds for the same `Q` agree up to a bijection `e : Fin k ≃ Fin k'`, with equality in `PositiveRankCuspidalClass F`. Not asserted (Markdown §6): anything at the infinite places, so GH Theorem 10.7.1 at every place is not stated; that `Q` is a constituent of a global induced representation; Langlands' Lemma 1, the admissibility of `Q` or the isotypy of its restrictions; that the spherical condition follows from the other two; a cuspidal-support map to `IsobaricData F`. |

Relation to earlier Library results. Before these modules the Library had
finite local components only for cuspidal realizations with a spectral
presentation (`CuspidalAllLocalIrreduciblePresentationExistenceStatement`,
proved) and for operator quotients with a supplied tensor presentation
(`OperatorQuotientTensorPresentation`, which does not assert that one
exists). It had the p-adic case of GH Theorem 11.5.2
(`UnitaryGenericLPolynomialNonvanishingStatement`, stated; since proved), convergence of
the partial pair Euler products on some right half-plane (namespace
`CuspidalPairEulerConvergence`), the line `Re s = 1` as the separate
`CuspidalPairBoundaryNonvanishingStatement`, and, of GH §10.7, the first half
of Theorem 10.7.1 (`CuspidalInducedConstituentAutomorphyStatement`) and
Theorem 10.7.2 (`CuspidalInducingDataRigidityStatement`), both stated.


| Exact target and the inputs of its proof | Proof in the Library |
| --- | --- |
| `LocalComponentExistenceStatement`. Route A: at one place, split the operators of `Q` into those at `v` and those away from `v`; on the finite-dimensional fixed-vector subspaces given by joint admissibility, an irreducible module over the tensor product of the two commuting algebras is a tensor product (GH, proof of Theorem 5.7.2 (ii), p.153; Burnside's theorem), which gives the isotypy and a model of the factor inside `Q.Space`. Route B: GH's proof of Theorem 6.3.7, p.166, through Lemma 6.3.6, the proved `flathRestrictedProductExistence` and GH Exercise 4.14. No other unproved Library statement is needed; joint admissibility is a hypothesis | `localComponentExistence` (`Langlands/Automorphic/LocalComponentExistenceProof.lean`) |
| `LocalComponentEmbeddingStatement`, through a proof of `LocalComponentExistenceStatement` and semisimple module theory (Mathlib's `isotypicComponent` and `IsIsotypicOfType`), at the infinite places for `(𝔤, K)`-modules; Flath, p.180 | `localComponentEmbedding` (`Langlands/Automorphic/LocalComponentEmbeddingProof.lean`) |
| `LocalComponentDeterminationStatement`, through proofs of the existence and embedding statements; for "⇐", the factorization of GH Theorem 6.3.7 (finite part through `flathRestrictedProductExistence`), the independence of restricted tensor products from the reference vectors (`RestrictedTensorReferenceIndependenceStatement`, since proved as `restrictedTensorReferenceIndependence`), and a criterion for intertwining the operator algebra on subquotients through its generators, which may need to be proved | `localComponentDetermination` (`Langlands/Automorphic/LocalComponentDeterminationProof.lean`) |
| The four elementary statements `RealPairLFactorRightHalfPlaneRegularityStatement`, `ComplexPairLFactorRightHalfPlaneRegularityStatement`, `RealUnitaryGenericPairRegularityReductionStatement` and `ComplexUnitaryGenericPairRegularityReductionStatement`, from `realLFactor_regular_iff`, `complexLFactor_regular_iff`, additivity of exponents in pair blocks and exponent arithmetic; no unproved Library statement | `realPairLFactorRightHalfPlaneRegularity` (`Langlands/Representation/Archimedean/RealPairLFactorRegularityProof.lean`); `complexPairLFactorRightHalfPlaneRegularity` (`Langlands/Representation/Archimedean/ComplexPairLFactorRegularityProof.lean`); `realUnitaryGenericPairRegularityReduction` (`Langlands/Representation/Archimedean/RealUnitaryGenericPairRegularityReductionProof.lean`); `complexUnitaryGenericPairRegularityReduction` (`Langlands/Representation/Archimedean/ComplexUnitaryGenericPairRegularityReductionProof.lean`) |
| `RealUnitaryGenericExponentBoundStatement` (the main work), then `RealUnitaryGenericPairRegularityStatement` from it and the four elementary statements. Route: the standard module is irreducible; Knapp–Vogan Theorem 0.6(a), p.7; Badulescu–Renard 2010, Theorems 8.1 and 8.2, p.1131, and Proposition 9.4; uniqueness in the Langlands classification (BR Theorem 3.3; Knapp 1994, Theorem 1). None of these classification theorems was in the Library at this commit | `realUnitaryGenericExponentBound` (`Langlands/Representation/Archimedean/RealUnitaryGenericExponentBoundProof.lean`); for `RealUnitaryGenericPairRegularityStatement` no theorem, but it follows from proved results: `realUnitaryGenericPairRegularityReduction` applied to `realUnitaryGenericExponentBound` (at both universes) and `realPairLFactorRightHalfPlaneRegularity` |
| `ComplexUnitaryGenericExponentBoundStatement`, then `ComplexUnitaryGenericPairRegularityStatement` from it and the four elementary statements. Route as in the real case, with Tadić's classification (BR Theorem 7.2, pp.1129–1131, and Proposition 9.1) and Knapp 1994, Theorem 4; the statement Markdown marks the `GL_n(ℂ)` bound as derived, since BR §8 is written for `GL(n, ℝ)` | `complexUnitaryGenericExponentBound` (`Langlands/Representation/Archimedean/ComplexUnitaryGenericExponentBoundProof.lean`); `complexUnitaryGenericPairRegularity` (`Langlands/Representation/Archimedean/ComplexUnitaryGenericPairRegularityProof.lean`) |
| `CuspidalSelfPairContinuationStatement`. Route A: the global Rankin–Selberg integral for `GL_r × GL_r` with an Eisenstein series (JS I (1.5), (3.17) and (4.6), p.555). Route B: from the published `CuspidalPairPoleStatement` (GH Theorem 11.7.1), after a twist to trivial split centre and division by finitely many local factors | `cuspidalSelfPairContinuation` (`Langlands/Global/Factors/CuspidalSelfPairContinuationProof.lean`) |
| `CuspidalPairAbsoluteConvergenceReductionStatement` (the main work), then `CuspidalPairAbsoluteConvergenceStatement` from it and `CuspidalSelfPairContinuationStatement`. Route of JS I, pp.555–557: local logarithms (5.3.1) with `UnramifiedUnitary.norm_characterValues_lt_sqrt` (JS I Corollary (2.5)); nonnegative coefficients for the self pair (5.3.3) through `eigenvalues_eq_map_inv_of_isContragredientOf`; Landau's theorem on Dirichlet series with nonnegative coefficients, to be proved with a source; Cauchy–Schwarz (5.3.5); `hasProd_of_summable_norm_sub_one` | `cuspidalPairAbsoluteConvergenceReduction` (`Langlands/Global/Factors/CuspidalPairAbsoluteConvergenceProof.lean`); `cuspidalPairAbsoluteConvergence` (`Langlands/Global/Factors/CuspidalPairAbsoluteConvergence.lean`) |
| `CuspidalSupportExistenceStatement`. Route of Langlands 1979, pp.204–205: constant terms along standard block parabolics (Lemma 4), Lemmas 5 and 6 (not in the Library at this commit), realization of `Q` in the space of `Ind δ^(-1) σ`, cuspidal blocks with presentations from `cuspidalIrreducibleAdmissibleFiniteSliceExistence`, and Lemma 1, p.203, or `LocalComponentEmbeddingStatement` (once proved) for the embeddings | `cuspidalSupportExistence` (`Langlands/Global/Factors/CuspidalSupportExistenceProof.lean`) |
| `CuspidalSupportUniquenessStatement`, through proofs of `IrreducibleSubquotientAdmissibilityStatement`, `LocalComponentExistenceStatement` and `LocalComponentEmbeddingStatement` and `CuspidalInducingDataRigidityStatement` (JS II Theorem (4.4)). The Library states and proves the reduction `CuspidalSupportUniquenessReductionStatement` (`CuspidalInducingDataRigidityStatement → CuspidalSupportUniquenessStatement`) in `Langlands/Global/Factors/CuspidalSupportUniquenessReduction.lean` | none recorded; conditional: from `CuspidalInducingDataRigidityStatement` (`cuspidalSupportUniqueness_of_rigidity`, `Langlands/Global/Factors/CuspidalSupportUniquenessReduction.lean`) |

The proof of `IsobaricStrongMultiplicityOneStatement` uses local-component determination; that
of `CuspidalStrongMultiplicityOneStatement` uses the real and complex cases of GH Theorem
11.5.2; that of `CuspidalSpectralRigidityStatement` uses the absolute convergence of partial
pair L-functions.

Further L4 targets. Of the list at the end of the previous section, the
first four items are stated here, the converse half of GH
Theorem 10.7.1 and GH Corollary 10.7.3 at the finite places only. Missing from the Library as
statements at this commit (later sections state some of them):

- GH Theorem 10.7.1 at every place (Langlands 1979, Lemma 1 and
  Proposition 2, pp.203–204), that is, the comparison of the archimedean
  components of `Q` with the archimedean inducing data;
- Flath's factorization of irreducible admissible representations of
  `GL_n(𝔸_F)` with the archimedean `(𝔤, K)`-modules (Flath 1979, Theorem 3,
  p.181), as a tensor product isomorphism; the new local-component statements
  give only its consequences at one place at a time;
- independence of the finite local components of a cuspidal realization from
  its spectral presentation;
- that the archimedean components of a unitary cuspidal realization satisfy
  the hypotheses of the archimedean statements above (unitarizability,
  genericity, a standard parameter), which the route to
  `CuspidalStrongMultiplicityOneStatement` needs;
- the cuspidal-support map from irreducible automorphic subquotients to
  `IsobaricData F`.

Of the target statements of this section, the table gives the Library's proofs; this note
records no proof of `RealUnitaryGenericPairRegularityStatement` or
`CuspidalSupportUniquenessStatement`; the first follows from proved results (`realUnitaryGenericPairRegularityReduction` with `realUnitaryGenericExponentBound` and `realPairLFactorRightHalfPlaneRegularity`), the second is derived only from `CuspidalInducingDataRigidityStatement` (`cuspidalSupportUniqueness_of_rigidity`).
Neither track of the program is complete.

## Archimedean components of cuspidal realizations and unitary central characters

This section was checked on 15 November 2026 against Library
`7229bb456a9afe1fc799771f6516c4b5dc9f976b`. It records two
statement modules. Neither module
introduces a definition. The first states that the standard module of an
archimedean place parameter of an actual cuspidal realization satisfies the
hypotheses of the archimedean case of Getz–Hahn Theorem 11.5.2. It also states
the resulting regularity of the archimedean pair factors on `Re s ≥ 1`. For a
given parameter, this is the fourth item of the list of L4 targets at
the end of the previous section. The second module derives the normalization
`HasUnitaryCentralCharacter` from `IsTrivialOnSplitCentre`. The second table gives the proofs
of their statements. Page numbers are printed pages; each
module's Markdown gives the PDF pages of the registered files.
Both modules first appeared in the Library at commit
`aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a`, and their files are the same there and at the
later commits `544dba09`, `9243fdc2` and `7229bb45`.

| Module | Exact content and boundary |
| --- | --- |
| [CuspidalArchimedeanComponentStatement](../../Langlands/Automorphic/CuspidalArchimedeanComponentStatement.md) | Six statements in namespace `Langlands.Automorphic`, for `T : CuspidalOperatorRealization F r` over a number field `F : Type u` with `CompactSpace (AdeleQuotient F)`. Each component statement assumes a place parameter. `T.realization.HasRealPlaceParameter v ds` gives `realRank ds = r + 1` and an injective map from `realStandardKFinite (r + 1) ds` into the realization that intertwines right translation by `O(r+1)` and right derivatives with the place actions at `v`. `HasComplexPlaceParameter v ds` is the complex analogue. `ArchimedeanStandardAdmissibleStatement` (derived) says that every real and every complex standard module (`realStandardRep n ds`, `complexStandardRep n ds`) is `IsAdmissibleGKModule`, with no rank hypothesis. `CuspidalArchimedeanStandardIrreducibleStatement.{u}`, `CuspidalArchimedeanStandardGenericStatement.{u}` and `CuspidalArchimedeanStandardUnitarizableStatement.{u}` (GH Theorem 11.3.6, p.298, and displays (11.14)–(11.17), pp.300–302) say that the standard module of the parameter is, respectively, `IsIrreducibleGKModule`, `IsRealGenericGKModule` (complex: `IsComplexGenericGKModule`) and `IsRealUnitarizableGKModule` (complex: `IsComplexUnitarizableGKModule`). The unitarizable statement also assumes `HasUnitaryCentralCharacter T`. `CuspidalArchimedeanPairRegularityStatement.{u}` is the entry (GH p.309, before Theorem 11.7.1, through Theorem 11.5.2, p.305). For `T`, `T'` with unitary central characters and parameters `ds`, `ds'` at the same infinite place, it says that `(realPairLFactor ds ds').denominator s ≠ 0` (complex: `complexPairLFactor`) whenever `1 ≤ Re s`. `CuspidalArchimedeanPairRegularityReductionStatement.{u}` says that the four component statements and the archimedean GH 11.5.2 entries at universes `0, 0` imply the entry. Not asserted (Markdown, "What is not asserted"): the existence of parameters, which is `CuspidalArchimedeanParameterExistenceStatement`; isomorphism classes of components beyond the four properties; anything at the finite places or for `Re s < 1`; the identification in Lean of the Library's pair factor with GH's |
| [CuspidalSplitCentreUnitaryStatement](../../Langlands/Global/Factors/CuspidalSplitCentreUnitaryStatement.md) | One statement, `Langlands.Global.CuspidalSplitCentreUnitaryCentralCharacterStatement.{u}` (derived from GH Lemma 2.6.2, p.69, and Theorem 6.5.3, p.169). For every actual cuspidal realization `T`, `CuspidalPairPoles.IsTrivialOnSplitCentre T` implies `HasUnitaryCentralCharacter T`. The hypothesis is invariance under `a I_(r+1)` for `a ∈ A_(G_m)` (GH (2.20), p.68). The statement links the normalization of `CuspidalPairPoleStatement` and `CuspidalIsobaricPoleOrderStatement` to the hypothesis of `isUnitarizable_of_hasUnitaryCentralCharacter`, of `CuspidalUnitaryLocalUnitarityStatement` and of the module above. Not asserted (Markdown, "What is not asserted"): the converse, which fails because `\|det\|^(iσ)` with `σ ≠ 0` is unitary and not trivial on `A_GL`; twisting an arbitrary realization to one trivial on `A_GL`; `L²` realizations or square integrability |

Relation to earlier Library results. Before these modules the Library already
proved `cuspidalArchimedeanWhittakerFunctional` and
`cuspidalArchimedeanIrreducibleAdmissibleComponent`. The first gives a
Whittaker functional on every nonzero place-stable subspace of a cuspidal
realization. The second gives an irreducible admissible place-stable subspace
at every infinite place. The Library also proved
`isUnitarizable_of_hasUnitaryCentralCharacter`, which gives one invariant
positive form on the whole realization. These three results concern subspaces
of the realization, not the standard module of a given parameter. The Library
stated the existence of parameters
(`CuspidalArchimedeanParameterExistenceStatement`, since proved as
`cuspidalArchimedeanParameterExistence`), with reductions to local
Langlands-quotient statements (`ArchimedeanParameterReduction`,
`CuspidalArchimedeanGenericComponentReduction`). It also stated the p-adic
analogues `CuspidalUnitaryLocalUnitarityStatement` and
`CuspidalUnitaryLocalGenericityStatement` (both since proved, as `cuspidalUnitaryLocalUnitarity`
and `cuspidalUnitaryLocalGenericity`).
`hasUnitaryCentralCharacter_of_associatedCentralCharacter` derives a unitary
central character from a different hypothesis, an associated Weil-group
representation. Library `7229bb45` had no lemma saying that
`realStandardKFinite n ds` is nonzero when `realRank ds = n`, or that
`complexStandardKFinite n ds` is nonzero when `ds.length = n`. If the carrier
were zero, a place parameter would exist for every realization. So the
genericity and irreducibility proofs need this fact.


| Exact target and the inputs of its proof | Proof in the Library |
| --- | --- |
| `CuspidalSplitCentreUnitaryCentralCharacterStatement`. Route: the central character `χ` of `T` (`existsUnique_hasCentralCharacter`, `centralCharacter_evaluate`); `χ = 1` on `A_(G_m)`, by evaluating at a point where some function of `T` is nonzero (`exists_evaluate_ne_zero`); every idele is `a · y` with `a ∈ A_(G_m)` and `y` of norm one (GH Lemma 2.6.2, p.69), with `a` built from the infinite ideles and `full_infiniteIdelesInclusion`; `‖χ‖` is trivial on the compact group `NormOneIdeleClasses` (`compactSpace_normOneIdeleClasses`). Only proved Library results are needed; a comparison lemma between the Library's two idele-class quotients may be required | `cuspidalSplitCentreUnitaryCentralCharacter` (`Langlands/Global/Factors/CuspidalSplitCentreUnitaryProof.lean`) |
| `ArchimedeanStandardAdmissibleStatement`. Route: the Iwasawa decomposition `g = diag(a) · u · k` of `GL_n(ℝ)` and `GL_n(ℂ)`, from `exists_upperTriangular_mul_unitary`; a function in the standard module is determined by its restriction to `K`; and `T ↦ (x ↦ (T x)(1))` embeds the intertwiner space into `Module.Dual ℂ (Fin d → ℂ)`. Only Mathlib and proved Library results are needed | `archimedeanStandardAdmissible` (`Langlands/Automorphic/ArchimedeanStandardAdmissibleProof.lean`) |
| `CuspidalArchimedeanStandardUnitarizableStatement` and `CuspidalArchimedeanPairRegularityReductionStatement`. Unitarizable: pull back the form of `isUnitarizable_of_hasUnitaryCentralCharacter` along the injective map of the parameter. This uses that the place actions at `v` are restrictions of the global compact and real Lie actions (`realPlaceLieAction_apply`, `realPlaceComplexLieInclusion_tmul`). Reduction: apply the archimedean GH 11.5.2 entries at universes `0, 0` with `A = LinearMap.id` (`isRealStandardIntertwiner_id`, `isComplexStandardIntertwining_id`). Only proved Library results are needed; the inputs of the reduction are hypotheses | `cuspidalArchimedeanStandardUnitarizable` (`Langlands/Automorphic/CuspidalArchimedeanComponentUnitaryProof.lean`); `cuspidalArchimedeanPairRegularityReduction` (`Langlands/Automorphic/CuspidalArchimedeanPairRegularityReductionProof.lean`) |
| `CuspidalArchimedeanStandardGenericStatement`, with a new reusable helper module proving `realStandardKFinite n ds ≠ ⊥` when `realRank ds = n` and `complexStandardKFinite n ds ≠ ⊥` when `ds.length = n`. Suggested construction: `f(g) = χδ(b(g)) Φ(k(g))`, with smooth Gram–Schmidt Iwasawa coordinates and a polynomial `Φ`. For an induction block of weight `m`, the `GL_2(ℝ)` raising and lowering operators show that the weights `\|k\| ≥ \|m\| + 1` span a subrepresentation, so the Fourier conditions hold. The image of the parameter is then a nonzero place-stable subspace, `cuspidalArchimedeanWhittakerFunctional` gives a Whittaker functional on it, and the pullback of that functional is the required one | `cuspidalArchimedeanStandardGeneric` (`Langlands/Automorphic/CuspidalArchimedeanStandardGenericProof.lean`) |
| `CuspidalArchimedeanStandardIrreducibleStatement`, the deep statement of the module. Route: nontriviality from the helper of the genericity proof. Isotypy of the realization at `v`: translates of the component given by `cuspidalArchimedeanIrreducibleAdmissibleComponent` under the operators away from `v`, which commute with the place actions as in `PlaceComponentExistence`, so the standard module is `W₀^(J)`. Multiplicity one, `\|J\| = 1`: either through BR Remark 2.3, Proposition 2.4 and Theorem 3.3(i), pp.1123–1125, with finite length from admissibility (`ArchimedeanStandardAdmissibleStatement`), or through a `K`-type of multiplicity one. The BR classification was not in the Library at this commit | `cuspidalArchimedeanStandardIrreducible` (`Langlands/Automorphic/CuspidalArchimedeanComponentIrreducibleProof.lean`) |
| `CuspidalArchimedeanPairRegularityStatement`. It assembles the proof of the reduction with proofs of the reduction's six hypotheses: admissibility, irreducibility, genericity and unitarizability above, and the archimedean GH 11.5.2 entries (`RealUnitaryGenericPairRegularityStatement`, `ComplexUnitaryGenericPairRegularityStatement`), which rest on the four elementary statements of the previous section | none recorded |

The proof of `CuspidalStrongMultiplicityOneStatement` uses the archimedean pair regularity and
the split-centre step.

Further L4 targets. The fourth item of the list at the end of the previous
section is stated here, for the standard module of a given place parameter. That item asks that the archimedean components of a unitary
cuspidal realization satisfy the hypotheses of the archimedean statements. The
existence of a parameter is the separate
`CuspidalArchimedeanParameterExistenceStatement`. Missing from the Library
as statements at this commit (the next section states some of them):

- GH Theorem 10.7.1 at every place (Langlands 1979, Lemma 1 and
  Proposition 2, pp.203–204);
- Flath's factorization of irreducible admissible representations of
  `GL_n(𝔸_F)` with the archimedean `(𝔤, K)`-modules, as a tensor product
  isomorphism (Flath 1979, Theorem 3, p.181); the isotypy at one infinite place, used in the
  irreducibility proof, is a part of it;
- the cuspidal-support map from irreducible automorphic subquotients to
  `IsobaricData F`.

Correction to the earlier lists. The lists of L4 targets at the end
of the three sections of 14 November 2026 ("isobaric automorphic
representations at every place", "admissibility of automorphic
representations" and "local components, absolute convergence, archimedean
Theorem 11.5.2, cuspidal support") name the independence of the finite local
components of a cuspidal realization from its spectral presentation. That item
is proved for irreducible components, so the list above omits it. The proof
was in none of the Libraries `4f6abf4c`, `c40a0134` and `4f4af6ba` against
which those sections were checked; it is in Library `7229bb45`. Module
`Langlands.Automorphic.AssociatedPresentationComparison` proves, among other results, three theorems in namespace
`CuspidalSpectralPresentation`, for two presentations `P`, `Q` of one actual
cuspidal realization `S`, in independent universes, and a finite place `v`.
`nonempty_localComponent_equiv` gives an equivalence between the local
representations `P.localComponent v` and `Q.localComponent v` when both are
irreducible. `localComponent_isoClass_eq` gives the equality of their smooth
isomorphism classes under the same hypotheses. `localComponent_padicClass_eq`
gives the equality of their classes in the canonical p-adic category when both
are also admissible. The irreducibility hypotheses remain. The module's
Markdown says that these lemmas alone do not handle the presentation without
irreducibility hypotheses in `AssociatedGammaStatement`.

Library `9243fdc2` differs from Library `544dba09` only in the Markdown
notes `notes/henniart/harris-cohomology-coverage.md` and
`notes/plancherel/actual-point-ledger.md` and in `wiki/README.md`. Library
`7229bb45` differs from Library `9243fdc2` only in the Markdown note
`notes/automorphic/l1-reductive-quotient-measure-coverage.md` and in
`wiki/README.md`.
Neither track of the program is complete.

## Cuspidal support at every place

This section was checked on 15 November 2026 against Library
`fab9caeae532b7a65e67e702bcab72d3194371ae`. It records one
statement module and a related admissibility result. The module states
two of the three items of the list of L4 targets at the end of the
previous section, GH Theorem 10.7.1 at every place and the cuspidal-support
map, and also the cuspidal support of isobaric sums. The second table gives the proofs of its
statements. Page numbers are printed pages; the module's
Markdown gives the PDF pages of the registered files. The
module first appeared in the Library at commit `fab9caea`.

| Module | Exact content and boundary |
| --- | --- |
| [CuspidalSupportEveryPlaceStatement](../../Langlands/Global/Factors/CuspidalSupportEveryPlaceStatement.md) | Four definitions and four statements, for a number field `F : Type u` with `CompactSpace (AdeleQuotient F)` and `Q : IrreducibleOperatorSubquotient F r`. `OperatorSubquotient.HasRealPlaceStandardConstituent v ds` (complex: `HasComplexPlaceStandardConstituent`) says that the blocks `ds` have total rank `n` and that some subspace `W` of `realStandardKFinite n ds`, stable under right translation by `O(n)` and right derivatives, maps linearly into `Q` intertwining these with the place actions at `v`, with nonzero image that has no other stable subspaces than `0` and itself. `Langlands.Global.IsInducedConstituent hm P h Q` for cuspidal data `T i` of `GL_(m i + 1)` with `∑ (m i + 1) = r + 1` is `IsFiniteInducedConstituent hm P h Q` together with, at every real (complex) place, parameters `ds i` of the `T i` (`HasRealPlaceParameter`, `HasComplexPlaceParameter`) such that `Q` has a standard constituent at `v` for `(List.ofFn ds).flatten`. `IrreducibleOperatorSubquotient.HasCuspidalSupport D`, for `D : IsobaricData F`, says that `Q` is an induced constituent of cuspidal data whose classes `⟨m i, (T i).isoClass⟩` form `D`. `CuspidalSupportEveryPlaceStatement.{u}` (Langlands 1979, Proposition 2, p.204, and Lemma 1, p.203; GH Theorem 10.7.1, pp.286–287): every `Q` is an induced constituent of some cuspidal data with presentations in universe `u`. `CuspidalSupportDataStatement.{u}` (GH Theorem 10.7.1, Corollary 10.7.3 and the sentence after it, p.287): every `Q` has exactly one `D` with `Q.HasCuspidalSupport.{u, u} D`. `CuspidalSupportDataReductionStatement.{u}`: `CuspidalSupportEveryPlaceStatement.{u}` and `CuspidalSupportUniquenessStatement.{u, u}` imply `CuspidalSupportDataStatement.{u}`. `CuspidalIsobaricSupportStatement.{u, uQ}` (GH Theorem 10.7.5 and (10.35), p.288): if `Q.IsCuspidalIsobaricSum T P h`, then `IsInducedConstituent hm P h Q`. Not asserted (Markdown §6): the first half of GH Theorem 10.7.1 at the infinite places; Langlands' Lemma 1, Flath's factorization, admissibility or isotypy of `Q`; independence of the predicates of the block order or the choice of parameters; that `Q` is determined by its cuspidal support; the converse of the isobaric statement; groups other than `GL_n` |

Relation to earlier Library results. The finite-place forms
`CuspidalSupportExistenceStatement` and `CuspidalSupportUniquenessStatement`
(module `Langlands.Global.Factors.CuspidalSupportStatement`) were already stated. The first conjunct of `IsInducedConstituent` is
`IsFiniteInducedConstituent`, so uniqueness at the finite places is the only
uniqueness input of the reduction. The existence of isobaric sums at every
place is `CuspidalIsobaricAutomorphyStatement`; with
`CuspidalIsobaricSupportStatement` such a sum has the multiset of its summands'
classes as cuspidal support, by the definition of `HasCuspidalSupport`. The
module does not import `OperatorSubquotientLocalComponentStatement`; its
Markdown §3 uses that module only to explain the archimedean predicates.


| Exact target and the inputs of its proof | Proof in the Library |
| --- | --- |
| `CuspidalSupportDataReductionStatement`. Route: existence from the witness data of the first hypothesis, with the multiset equation by `rfl`; uniqueness from the bijection `e` of index sets given by the second hypothesis applied to the finite conjuncts, then `Multiset.map_map` and `Multiset.map_univ_val_equiv`. Both inputs are hypotheses | `cuspidalSupportDataReduction` (`Langlands/Global/Factors/CuspidalSupportDataReductionProof.lean`) |
| `CuspidalSupportEveryPlaceStatement`, the deep statement of the module. Route: Langlands' global realization of `Q` as a quotient of a subspace of `Ind δ^(-1) σ` with cuspidal blocks (Lemmas 4–6, pp.204–205), built once as a helper; the finite places as for `CuspidalSupportExistenceStatement`; at an infinite place, parameters of the blocks (`CuspidalArchimedeanParameterExistenceStatement`), irreducibility of their standard modules (`CuspidalArchimedeanStandardIrreducibleStatement`) and isotypy of local restrictions; the `K_v`-finite induced space as `I((List.ofFn ds).flatten) ⊗ M` by induction in stages; and an irreducible `(𝔤_v, K_v)`-submodule `J` of `Q` (admissibility and the local-component statements) written as `W / W'` through a flag with one-dimensional steps in a finite-dimensional part of `M`. the route needs Langlands' Lemmas 5 and 6, the factorization of the global induced space and the archimedean isotypy of cuspidal realizations as helper results | `cuspidalSupportEveryPlace` (`Langlands/Global/Factors/CuspidalSupportEveryPlaceProof.lean`) |
| `CuspidalIsobaricSupportStatement`. Route: at the finite places, the local isobaric sum is a subquotient of `canonicalNormalizedProductInduced` (Tadić Proposition A.4(ii), proved as `langlandsHeadProductSubquotient`; as in the route to `CuspidalIsobaricRealizationStatement`), with sphericity outside `S` by GH Theorem 10.6.3; at the real and complex places, the Langlands quotient of the standard module of the reordered blocks is a subquotient of `I((List.ofFn ds).flatten)`, because standard modules of reordered blocks have the same composition factors (BR Remark 2.3 and Proposition 2.4, pp.1123–1124). Finite length and the Grothendieck group of archimedean standard modules were not in the Library at this commit | `cuspidalIsobaricSupport` (`Langlands/Global/Factors/CuspidalIsobaricSupportProof.lean`) |
| `CuspidalSupportDataStatement`, the entry point. It applies the proof of the reduction to proofs of `CuspidalSupportEveryPlaceStatement` and `CuspidalSupportUniquenessStatement` | none recorded; conditional: from `CuspidalSupportUniquenessStatement` and the proved `CuspidalSupportEveryPlaceStatement` (`cuspidalSupportDataReduction`, `Langlands/Global/Factors/CuspidalSupportDataReductionProof.lean`) |

The real admissibility proof. Module `Langlands.Representation.Archimedean.RealStandardModuleAdmissible`,
which first appeared at Library commit `fab9caea`, proves
`Langlands.Archimedean.realStandardAdmissible : RealStandardAdmissibleStatement`,
where `RealStandardAdmissibleStatement` is `∀ (n : ℕ) (ds : List RealBlock),
IsAdmissibleGKModule (realStandardRep n ds)`. That is the first conjunct of
`ArchimedeanStandardAdmissibleStatement` (previous section). The proof follows the route given
there: the Iwasawa
decomposition `exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact`,
determination by the restriction to `O(n)`, and the injective evaluation map
`gkIntertwinerValueAtOne`; the helpers `finrank_gkIntertwiners_kFiniteRep_le`
and `isAdmissibleGKModule_kFiniteRep` hold for any right-translation-stable
subspace of a real principal series. The complex conjunct (`complexStandardRep`, `U(n)`) was
then the remaining part; the Library now proves `ArchimedeanStandardAdmissibleStatement`, as
`archimedeanStandardAdmissible` (`Langlands/Automorphic/ArchimedeanStandardAdmissibleProof.lean`).

Further L4 targets. The first and third items of the list at the end of the
previous section (GH Theorem 10.7.1 at every place and the cuspidal-support
map) are stated here. Missing from the Library as a
statement at this commit is Flath's factorization of irreducible admissible representations
of `GL_n(𝔸_F)` with the archimedean `(𝔤, K)`-modules, as a tensor product
isomorphism (Flath 1979, Theorem 3, p.181).
Neither track of the program is complete.

## Proof routes for the L4 targets

This section was checked on 15 November 2026 against Library
`72480b70c88adff84a438bd7029d64ee3977469c`. It records proof routes for targets of the previous
sections. Every main theorem below uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

Complete proofs. Each of the following has exactly the target type, and each is in the Library:

| Target | Main theorem and helper modules |
| --- | --- |
| `CuspidalSplitCentreUnitaryCentralCharacterStatement` | `Langlands.Global.cuspidalSplitCentreUnitaryCentralCharacter`, module `Langlands.Global.Factors.CuspidalSplitCentreUnitaryProof`; helper `Langlands.Global.HeckeCharacterPositiveRealUnitary` (`HeckeCharacter.isUnitary_of_positiveRealIdeles`) |
| `ArchimedeanStandardAdmissibleStatement` | `Langlands.Automorphic.archimedeanStandardAdmissible`, module `Langlands.Automorphic.ArchimedeanStandardAdmissibleProof`. The real conjunct is `realStandardAdmissible` (previous section). The complex conjunct `Langlands.Archimedean.complexStandardAdmissible` is declared in the same module. It applies `PrincipalSeries.isAdmissibleGKModule_principalSeriesRep` of the helper `Langlands.Representation.Archimedean.PrincipalSeriesAdmissible`, which proves admissibility of the principal series by the same route, for `U(n)` |
| The four elementary statements of GH 11.5.2 (archimedean) | `realPairLFactorRightHalfPlaneRegularity`, `complexPairLFactorRightHalfPlaneRegularity`, `realUnitaryGenericPairRegularityReduction`, `complexUnitaryGenericPairRegularityReduction` (namespace `Langlands.Archimedean`), one module each under `Langlands/Representation/Archimedean/`, with the helper `PairBlockExponent` |
| `CuspidalArchimedeanStandardUnitarizableStatement`, `CuspidalArchimedeanPairRegularityReductionStatement` | `Langlands.Automorphic.cuspidalArchimedeanStandardUnitarizable` (module `CuspidalArchimedeanComponentUnitaryProof`) and `cuspidalArchimedeanPairRegularityReduction` (module `CuspidalArchimedeanPairRegularityReductionProof`) |
| `CuspidalSupportDataReductionStatement` | `Langlands.Global.cuspidalSupportDataReduction`, module `Langlands.Global.Factors.CuspidalSupportDataReductionProof` |
| `LocalComponentExistenceStatement` | `Langlands.Automorphic.localComponentExistence`, module `Langlands.Automorphic.LocalComponentExistenceProof`. The finite places are handled in `LocalComponentFinitePlace` (with the helper `Langlands.Representation.Smooth.JointIsotypicComponent`), the real and complex places in `OperatorSubquotientPlaceComponent` and `OperatorSubquotientPlaceComponentComplex`. The last two port the Library's place-component results for cuspidal realizations to operator subquotients |
| `CuspidalPairAbsoluteConvergenceReductionStatement` (JS I Theorem (5.3) from Lemma (5.2)) | `Langlands.Global.cuspidalPairAbsoluteConvergenceReduction`, module `Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceProof`, with two helper modules. `Langlands.Analysis.LandauDirichlet` proves Landau's theorem for general Dirichlet series with nonnegative coefficients (Hardy–Riesz 1915, Theorem 10, p.10, registered as `hardy-riesz-1915-dirichlet-series`), also in the exponential form used by JS I, p.556. `Langlands.Representation.Unramified.UnitarySpectrumConjugation` proves that a unitarizable spherical representation with spectrum `s` has `conj s = s⁻¹`. The bound `\|α\| ≤ q_v^(1/2)` comes from the published `norm_unramifiedClass_le_sqrt`. The second target, `CuspidalPairAbsoluteConvergenceStatement`, also needs `CuspidalSelfPairContinuationStatement`; both are proved (`cuspidalPairAbsoluteConvergence`, `cuspidalSelfPairContinuation`) |
| `ArthurCombinatoricsStatement` | `Langlands.ArthurCombinatorics.arthurCombinatoricsStatement`, module `Langlands.LinearAlgebra.ArthurCombinatoricsProof`, with the six conjuncts as named theorems in five helper modules `ArthurCombinatorics{Alternating,CartanInverse,Sigma,SigmaSupport,LanglandsLemma}` |

Reductions. Each proves the target from the named inputs, or proves part of it.

| Target | Reduction and inputs | In the Library |
| --- | --- | --- |
| `CuspidalIsobaricPoleOrderStatement` (GH Lemma 11.8.1) | From `CuspidalPairPoleStatement`, `CuspidalPairBoundaryNonvanishingStatement` and `CuspidalSplitCentreUnitaryCentralCharacterStatement`. The route proves the identity theorem on a half-plane, the splitting of the Euler product at `S` with the unramified comparison of L-polynomials, nonpositive orders of all local factors, Shahidi at `s = 1`, order additivity, and the symmetry of the contragredient relation for cuspidal realizations with unitary central characters (`Langlands.Automorphic.CuspidalOperatorRealization.isContragredientOf_symm`, module `Langlands.Automorphic.ContragredientSymmetry`, through the Library's unitary criterion `isContragredientOf_of_unitaryForm`) | `isContragredientOf_symm` is in the Library; this note records no reduction theorem for the target, and no proof of it. The Library now has two reductions: `cuspidalIsobaricPoleOrderReduction`, from `CuspidalPairPoleStatement` and `CuspidalPairBoundaryNonvanishingStatement`, and `cuspidalIsobaricPoleOrderLandauReduction`, from `CuspidalPairPoleStatement` alone |
| `CuspidalStrongMultiplicityOneStatement` (GH Theorem 11.7.2) | From `CuspidalEulerConstituentRecoveryStatement`, with one constituent on each side. The bridge of §5 of the statement Markdown: equal finite local classes at unramified places give equal Satake spectra, by the Library's `Unramified.sphericalSpectrumUniqueness` | This reduction is not in the Library under the name `cuspidalStrongMultiplicityOne_of_eulerConstituentRecovery`; the Library has the conditional `cuspidalStrongMultiplicityOne_of_nondualPartialEulerContinuation` |
| `CuspidalSpectralRigidityStatement` (JS II Theorems 4.2 and 4.4) | From `CuspidalPowerTraceIndependenceStatement` (JS II Theorem 4.2, the first conjunct of the target): constituent recovery with multiplicities by the multiplicity comparison of the proof of Theorem 4.4, the Euler form, and the comparison of systems attached to one class | `cuspidalSpectralRigidity_of_independence` (`Langlands/Automorphic/Unramified/CuspidalSpectralRigidityReduction.lean`); this note records no proof of the input, which the Library derives from the proved `CuspidalPairAbsoluteConvergenceStatement` and the logarithmic asymptotics `CuspidalPairLogAsymptoticsAt` (`cuspidalPowerTraceIndependence_of_pairLogAsymptotics`) |
| `LocalComponentEmbeddingStatement` | From `LocalComponentExistenceStatement` | `localComponentEmbedding_of_localComponentExistence` (`Langlands/Automorphic/LocalComponentEmbeddingReduction.lean`); the target is proved |
| `LocalComponentDeterminationStatement` | The forward implication of the target, from `LocalComponentExistenceStatement`; the reverse implication is the tensor factorization | `localComponentDetermination_forward` (`Langlands/Automorphic/LocalComponentDeterminationForward.lean`); the target is proved |
| `CuspidalSupportUniquenessStatement` | From `IrreducibleSubquotientAdmissibilityStatement`, `LocalComponentExistenceStatement` and `CuspidalInducingDataRigidityStatement` | Not in the Library under the name `cuspidalSupportUniqueness_of_localComponentExistence`; the Library has `cuspidalSupportUniqueness_of_rigidity` (`Langlands/Global/Factors/CuspidalSupportUniquenessReduction.lean`) |
| `GeneratedFormAdmissibilityStatement` | From `HarishChandraFinitenessStatement` | `generatedFormAdmissibility_of_harishChandraFiniteness` (`Langlands/Automorphic/GeneratedFormAdmissibilityReduction.lean`); the target is proved |
| `CuspidalInducingDataRigidityStatement` (GH Theorem 10.7.2) | From `CuspidalEulerConstituentRecoveryStatement` alone, with the local input `UnramifiedProductInducedSpectrumStatement`: at a finite place, a spherical subquotient of `i(σ_1, …, σ_k)` with spherical blocks `σ_i` of spectra `s_i` has the concatenated spectrum (the first step of the proof of JS II Theorem 4.4, p.809) | `cuspidalInducingDataRigidity_of_constituentRecovery` (`Langlands/Global/Factors/CuspidalInducingDataRigidityReduction.lean`); this note records no proof of its inputs; the Library derives the first from `CuspidalPowerTraceConstituentRecoveryStatement` (`cuspidalEulerConstituentRecovery_of_powerTraceRecovery`) |
| `IrreducibleSubquotientAdmissibilityStatement` (Borel–Jacquet §4.6) | From `GeneratedFormAdmissibilityStatement`. An irreducible operator subquotient is the image of the realization generated by one automorphic form, and joint admissibility passes to quotients. The quotient step uses the Library's compact Maschke lifting lemma and averaging over a compact open subgroup | `irreducibleSubquotientAdmissibility_of_generatedFormAdmissibility` (`Langlands/Automorphic/IrreducibleSubquotientAdmissibilityReduction.lean`); the target is proved |
| `CuspidalSelfPairContinuationStatement` (JS I Lemma (5.2)) | `CuspidalPairPoleStatement → CuspidalSelfPairContinuationStatement`, route B above, with helper modules `Langlands.Analysis.ContinuousCharacterReal` (continuous unitary characters of `ℝ` are `u ↦ exp(itu)`) and a split-centre twist by `\|det\|^(is)` to reach realizations trivial on the split centre, with the conjugate realization realizing the contragredient. Possible zeros of the archimedean denominators are handled by the identity theorem | The target is proved, as `cuspidalSelfPairContinuation` (`Langlands/Global/Factors/CuspidalSelfPairContinuationProof.lean`); `ContinuousCharacterReal` is in the Library |

Consequences for the L4 targets. By these routes, strong multiplicity one for cuspidal
realizations (GH Theorem 11.7.2) depends
only on JS II Theorem 4.2. That theorem rests on the asymptotics of JS II
Theorem 4.1. Those need JS I Theorem 5.3, which depends only on GH Theorem 11.7.1, and the pole
at `s = 1` (GH Theorem 11.7.1, with local regularity) and Shahidi's
nonvanishing. GH Lemma 11.8.1 depends only on GH Theorem 11.7.1 and Shahidi's theorem. GH
Theorem 10.7.2 depends only on JS II Theorem
4.2. The admissibility of irreducible
automorphic subquotients (Borel–Jacquet §4.6) depends only on Harish-Chandra's
finiteness theorem; both are proved. The existence of
local components at every place is the input of local-component embedding and determination
and of cuspidal-support uniqueness.
Neither track of the program is complete.

## Finite pair regularity, totally complex forms and routes through the analytic inputs

This section was checked on 17 November 2026 against Library
`314cfd1a0275806b9ff4281f3d3e51a05e9a6cb5`. Every main theorem named below was checked to use
only `propext`, `Classical.choice` and `Quot.sound`.

### Statements and proofs added since the previous section

- `Langlands.Global.CuspidalFinitePairRegularityStatement` (module
  `Langlands.Global.Factors.CuspidalFinitePairRegularityStatement`; Getz–Hahn
  Theorem 11.5.2, non-Archimedean case, in the normalization of the pole
  statement). The Library proves it, as `cuspidalFinitePairRegularity`
  (`Langlands/Global/Factors/CuspidalFinitePairRegularityProof.lean`; next section).
- `Langlands.ArthurCombinatorics.arthurCombinatoricsStatement` (module
  `Langlands.LinearAlgebra.ArthurCombinatoricsProof`), the proof of
  `ArthurCombinatoricsStatement`.
- Totally complex forms of Harris-branch inputs,
  each the original proposition with `[NumberField.IsTotallyComplex F]`
  inserted after `[NumberField F]`. Two of them are inputs of this program's
  L4 targets: `Langlands.Global.CuspidalPairPoleTCStatement` (module
  `Langlands.Global.Factors.CuspidalPairPoleTCStatement`)
  and `Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement`
  (module of the same name). This note records no proof of
  `CuspidalPairPoleTCStatement` (the Library now derives it from `CuspidalPairCompletedEquationTCStatement`
  and the normalized continuation over each totally complex field, by `cuspidalPairPoleTCReduction`); for `CuspidalSpectralRigidityTCStatement` the Library has the
  conditional `cuspidalSpectralRigidityTC_of_normalizedContinuation`
  (`Langlands/Automorphic/Unramified/CuspidalSpectralRigidityTCPoleProfileReduction.lean`).

### Routes from the four analytic inputs

The four inputs are `CuspidalPairPoleStatement` (GH Theorem 11.7.1),
`CuspidalPairBoundaryNonvanishingStatement` (Shahidi 1981, Theorem 5.2),
`Automorphic.CuspidalArchimedeanPairRegularityStatement` and
`RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement` (GH Theorem 11.5.2, p-adic case).

| Target | Route and inputs | In the Library |
| --- | --- | --- |
| `CuspidalSpectralRigidityStatement` (JS II Theorems 4.1, 4.2 and the numerical step of 4.4) | From the four inputs. The same route proves `CuspidalSpectralRigidityTCStatement` from the same inputs with `CuspidalPairPoleTCStatement` in place of `CuspidalPairPoleStatement`. To do so it restates the proofs over one number field (helper module `Langlands.Global.Factors.CuspidalPairPoleFieldwise`). JS I Lemma (5.2) and Theorem (5.3) are derived from the pole statement over the field of the conclusion, through the proofs of `CuspidalSelfPairContinuationStatement` and `CuspidalPairAbsoluteConvergenceReductionStatement`; JS II Theorem 4.1 is read off the completed L-function of GH Theorem 11.7.1, with Shahidi's theorem on `Re s = 1`. The finite regularity statement is derived from `UnitaryGenericLPolynomialNonvanishingStatement` by `Langlands.Global.cuspidalFinitePairRegularity_of_unitaryGeneric` | `CuspidalPairPoleFieldwise` is in the Library (`Langlands/Global/Factors/CuspidalPairPoleFieldwise.lean`); the theorems `cuspidalSpectralRigidity_of_published_inputs` and `cuspidalSpectralRigidityTC_of_published_inputs` of this route are not; this note records no proof of the target. The Library now derives the target from `CuspidalPairPoleStatement`, and its totally complex form from `CuspidalPairPoleTCStatement`, by `cuspidalSpectralRigidityLandauReduction` (`Langlands/Automorphic/Unramified/CuspidalSpectralRigidityLandauReduction.lean`) with the proved `cuspidalPairAbsoluteConvergence` |
| `CuspidalStrongMultiplicityOneStatement` (GH Theorem 11.7.2) | From the four inputs, through the reduction to `CuspidalEulerConstituentRecoveryStatement` (previous section) | `cuspidalStrongMultiplicityOne_of_published_inputs` is not in the Library; the Library has the conditional `cuspidalStrongMultiplicityOne_of_nondualPartialEulerContinuation` (`Langlands/Global/Factors/CuspidalStrongMultiplicityOnePoleReduction.lean`) |
| `CuspidalInducingDataRigidityStatement` (GH Theorem 10.7.2) | From the four inputs, through the reduction to `CuspidalEulerConstituentRecoveryStatement` (previous section) | `cuspidalInducingDataRigidity_of_published_inputs` is not in the Library; the reduction `cuspidalInducingDataRigidity_of_constituentRecovery` is; this note records no proof of the target |
| `CuspidalIsobaricPoleOrderStatement` (GH Lemma 11.8.1) | From `CuspidalPairPoleStatement` and `CuspidalPairBoundaryNonvanishingStatement` only; the input `CuspidalSplitCentreUnitaryCentralCharacterStatement` is discharged by its proof `cuspidalSplitCentreUnitaryCentralCharacter` | `cuspidalIsobaricPoleOrder_of_published_inputs` is not in the Library; this note records no proof of the target. The Library now derives it from the two inputs (`cuspidalIsobaricPoleOrderReduction`) and from `CuspidalPairPoleStatement` alone (`cuspidalIsobaricPoleOrderLandauReduction`) |
| `CuspidalFinitePairRegularityStatement` (finite pair regularity) | `Langlands.Global.cuspidalFinitePairRegularity_of_unitaryGeneric : UnitaryGenericLPolynomialNonvanishingStatement.{u, u, u} → CuspidalFinitePairRegularityStatement.{u, uQ}`, via the proved `cuspidalUnitaryLocalGenericity`, `cuspidalUnitaryLocalUnitarity` and `genericLanglandsQuotientLFactor` (JPSS 1983, Proposition (9.4), display (4)) | `cuspidalFinitePairRegularity_of_unitaryGeneric` (`Langlands/Global/Factors/CuspidalFinitePairRegularityProof.lean`); the target is proved |

### Consequences for the L4 targets

By these routes:

- GH Theorem 11.7.2 (strong multiplicity one), GH Theorem 10.7.2 (rigidity of
  cuspidal inducing data) and the three conjuncts of Jacquet–Shalika rigidity
  depend only on the four inputs;
- the totally complex form of Jacquet–Shalika rigidity (Harris's input 9)
  depends only on a proof of `CuspidalPairPoleTCStatement` and the last three
  of the four inputs;
- GH Lemma 11.8.1 depends only on `CuspidalPairPoleStatement` and
  `CuspidalPairBoundaryNonvanishingStatement`.

For these targets, the statements named in the three items are the remaining
analytic inputs. Of them the Library proves `UnitaryGenericLPolynomialNonvanishingStatement`
(next section); this note records no proof of the others (for `CuspidalPairPoleStatement`
the Library has only the conditional `cuspidalPairPole_of_covering_normalized_products`). Of
the other inputs recorded in earlier sections, Harish-Chandra's finiteness theorem is proved,
as `harishChandraFiniteness` (`Langlands/Automorphic/HarishChandraFinitenessProof.lean`); the
truncation block of the L3 foundations is described in the
[Arthur foundations ledger](arthur-l3-foundations-coverage.md). Neither track of the program is
complete.

## Getz–Hahn Theorem 11.5.2, p-adic case, and finite pair regularity

This section was checked on 17 November 2026 against Library
`fcb85a7ef43356fec01e6ccf1605f08568c08cb0`. Every theorem
named below was checked to use only `propext`, `Classical.choice` and `Quot.sound`.

### Proofs without hypotheses

| Target | Main theorem and modules | In the Library |
| --- | --- | --- |
| `UnitaryGenericLPolynomialNonvanishingStatement` (GH Theorem 11.5.2, p-adic case) | `Langlands.RankinSelberg.UnitaryGeneric.unitaryGenericLPolynomialNonvanishing : UnitaryGenericLPolynomialNonvanishingStatement.{uF, uV, uW}`, with no hypotheses. Seven modules under `Langlands/Representation/RankinSelberg/`: `UnitaryWhittakerTorusSum` (Jacquet–Shalika I, (1.3.1), in torus form, from the published `padicCellBound`), `UnitaryWhittakerRestriction`, `UnitaryWeightedWhittakerSquare` (exponents `a ≥ 1/2`), `UnitaryEqualRankAnalytic` and `UnitaryZeroRowAnalytic` (convergence on `Re s ≥ 1`, holomorphy on `Re s > 1`), `BoundaryRationalRegularity` (regularity of rational continuations on `Re s = 1` from boundedness on a strip) and the assembly `UnitaryGenericLPolynomialNonvanishingProof`. The proof also proves the published `UnitaryEqualRankConvergenceStatement` (Jacquet–Shalika I, Proposition (1.5)(i)) as `unitaryEqualRankConvergence` | `unitaryGenericLPolynomialNonvanishing` (`Langlands/Representation/RankinSelberg/UnitaryGenericLPolynomialNonvanishingProof.lean`) and `unitaryEqualRankConvergence` (`UnitaryEqualRankAnalytic.lean`); all seven modules are in the Library |
| `CuspidalFinitePairRegularityStatement` (finite pair regularity) | `Langlands.Global.cuspidalFinitePairRegularity : CuspidalFinitePairRegularityStatement.{u, uQ}`, with no hypotheses: the reduction of the previous section applied to the proof above | `cuspidalFinitePairRegularity` (`Langlands/Global/Factors/CuspidalFinitePairRegularityProof.lean`) |

### Routes from the three remaining analytic inputs

With the p-adic case of GH Theorem 11.5.2 proved, the routes of the previous section need only
`CuspidalPairPoleStatement`, `CuspidalPairBoundaryNonvanishingStatement` and
`CuspidalArchimedeanPairRegularityStatement`:

| Target | Main theorem of the route and its inputs | In the Library |
| --- | --- | --- |
| `CuspidalSpectralRigidityStatement` and `CuspidalSpectralRigidityTCStatement` | `cuspidalSpectralRigidity_of_analytic_inputs` and `cuspidalSpectralRigidityTC_of_analytic_inputs`: the target from the three inputs, and its totally complex form with `CuspidalPairPoleTCStatement` in place of `CuspidalPairPoleStatement` | Neither theorem is in the Library; this note records no proof of the targets. The Library now derives them from `CuspidalPairPoleStatement` and `CuspidalPairPoleTCStatement` alone, by `cuspidalSpectralRigidityLandauReduction` with the proved `cuspidalPairAbsoluteConvergence` |
| `CuspidalStrongMultiplicityOneStatement` | `cuspidalStrongMultiplicityOne_of_analytic_inputs`, from the three inputs | Not in the Library |
| `CuspidalInducingDataRigidityStatement` | `cuspidalInducingDataRigidity_of_analytic_inputs`, from the three inputs | Not in the Library |

### Consequences

By these routes, Jacquet–Shalika rigidity, strong
multiplicity one (GH Theorem 11.7.2) and the rigidity of cuspidal inducing data
(GH Theorem 10.7.2) depend only on `CuspidalPairPoleStatement`,
`CuspidalPairBoundaryNonvanishingStatement` and `CuspidalArchimedeanPairRegularityStatement`.
The totally complex form of Jacquet–Shalika rigidity (Harris's input 9)
depends only on a proof of `CuspidalPairPoleTCStatement` and the last two of these. This note
records no proof of these three remaining statements. Neither track of the
program is complete.

## Proved L4 inputs, local-component determination and the fieldwise forms

This section was checked on 17 November 2026 against Library
`ab9053b1751d6b6557d044c38c04e4c8a67dfffc`. Every theorem named
below was checked to use only `propext`, `Classical.choice` and `Quot.sound`.

### Proofs that entered the Library by commit `ab9053b1`

| Target | Proof in the Library |
| --- | --- |
| `UnitaryGenericLPolynomialNonvanishingStatement` (GH Theorem 11.5.2, p-adic case) | `unitaryGenericLPolynomialNonvanishing` (`Langlands/Representation/RankinSelberg/UnitaryGenericLPolynomialNonvanishingProof.lean`) |
| `CuspidalSplitCentreUnitaryCentralCharacterStatement` | `cuspidalSplitCentreUnitaryCentralCharacter` (`Langlands/Global/Factors/CuspidalSplitCentreUnitaryProof.lean`) |
| `ArchimedeanStandardAdmissibleStatement` | `archimedeanStandardAdmissible` (`Langlands/Automorphic/ArchimedeanStandardAdmissibleProof.lean`) |
| `CuspidalArchimedeanStandardUnitarizableStatement` and `CuspidalArchimedeanPairRegularityReductionStatement` | `cuspidalArchimedeanStandardUnitarizable` (`Langlands/Automorphic/CuspidalArchimedeanComponentUnitaryProof.lean`) and `cuspidalArchimedeanPairRegularityReduction` (`Langlands/Automorphic/CuspidalArchimedeanPairRegularityReductionProof.lean`) |
| `CuspidalSupportDataReductionStatement` | `cuspidalSupportDataReduction` (`Langlands/Global/Factors/CuspidalSupportDataReductionProof.lean`) |
| `LocalComponentExistenceStatement` | `localComponentExistence` (`Langlands/Automorphic/LocalComponentExistenceProof.lean`) |
| Right half-plane regularity of real and complex pair L-factors, and the reductions of GH Theorem 11.5.2 (archimedean) to the exponent bounds (four targets) | `realPairLFactorRightHalfPlaneRegularity`, `complexPairLFactorRightHalfPlaneRegularity`, `realUnitaryGenericPairRegularityReduction`, `complexUnitaryGenericPairRegularityReduction` (`Langlands/Representation/Archimedean/{RealPairLFactorRegularityProof,ComplexPairLFactorRegularityProof,RealUnitaryGenericPairRegularityReductionProof,ComplexUnitaryGenericPairRegularityReductionProof}.lean`) |
| `CuspidalPairAbsoluteConvergenceReductionStatement` (JS I Theorem (5.3) from Lemma (5.2)) | `cuspidalPairAbsoluteConvergenceReduction` (`Langlands/Global/Factors/CuspidalPairAbsoluteConvergenceProof.lean`) |

The second statement of the same source, `CuspidalPairAbsoluteConvergenceStatement`, is
also proved, as `cuspidalPairAbsoluteConvergence`
(`Langlands/Global/Factors/CuspidalPairAbsoluteConvergence.lean`). The proof of finite pair
regularity (module `Langlands.Global.Factors.CuspidalFinitePairRegularityProof`) and the four
helper modules for the real-place nonvanishing of standard modules (next section) were not yet
in Library `ab9053b1`; both are in the Library now.

### Local-component determination and embedding

| Target | Main theorem and modules | In the Library |
| --- | --- | --- |
| `LocalComponentDeterminationStatement` (GH Theorem 6.3.7 and the uniqueness of the factors; Flath Theorem 3) | `Langlands.Automorphic.localComponentDetermination : LocalComponentDeterminationStatement.{u}`, with no hypotheses, from `localComponentExistence`. Seven modules: `OpenSubgroupInduction` (open subgroups of `GL_n(𝔸_f)`, induction over local factors), `CommutingFamilyUniqueness` (an abstract uniqueness theorem for commuting, jointly irreducible families of isotypic actions with scalar self-intertwiners, almost-everywhere spherical lines and smooth vectors), `FreeMonoidGenerators` (the place actions read as free-monoid representations; common isotypic types), `OperatorSubquotientPlaceGeneration` (the place actions generate the operator algebra), and the forward, reverse and final modules `LocalComponentDetermination{Forward,Reverse,Proof}`. The reverse implication does not build the restricted tensor factorization; it uses the same inputs (isotypy at each place, Schur, one-dimensional spherical lines, smoothness) in the abstract theorem | `localComponentDetermination` (`Langlands/Automorphic/LocalComponentDeterminationProof.lean`); the modules are `Langlands/Global/FiniteAdelicGL/OpenSubgroupInduction.lean`, `Langlands/Representation/{CommutingFamilyUniqueness,FreeMonoidGenerators}.lean`, `Langlands/Automorphic/OperatorSubquotientPlaceGeneration.lean` and `Langlands/Automorphic/LocalComponentDetermination{Forward,Reverse,Proof}.lean` |
| `LocalComponentEmbeddingStatement` | `Langlands.Automorphic.localComponentEmbedding`, importing the modules of the proof of `LocalComponentExistenceStatement` | `localComponentEmbedding` (`Langlands/Automorphic/LocalComponentEmbeddingProof.lean`) |

`CuspidalArchimedeanStandardGenericStatement` (genericity of archimedean standard-module
components of cuspidal realizations) is proved, as `cuspidalArchimedeanStandardGeneric`
(`Langlands/Automorphic/CuspidalArchimedeanStandardGenericProof.lean`).

### Fieldwise forms

The routes of the previous sections to Jacquet–Shalika rigidity, GH Theorem 11.7.2 and GH
Theorem 10.7.2 use fieldwise forms of two modules of the Library,
`Langlands.Automorphic.ContragredientUniqueness` and
`Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceProof`; they are kept in separate
modules (next section). The remaining inputs of these routes are
`CuspidalPairPoleStatement` (or `CuspidalPairPoleTCStatement` for the totally
complex form), `CuspidalPairBoundaryNonvanishingStatement` and
`CuspidalArchimedeanPairRegularityStatement`.

### Consequences

- The local-component block of statement module
  `Langlands.Automorphic.OperatorSubquotientLocalComponentStatement` is
  covered: the Library proves existence, embedding and determination (above).
  Step 1 of the expected route to strong multiplicity one for isobaric
  representations (`IsobaricStrongMultiplicityOneStatement`, GH Corollary 11.7.3) therefore has
  all its local-component inputs; this note records no proof of that statement.
- By the routes of the previous sections, the
  rigidity theorems and GH Theorem 11.7.2 depend only on `CuspidalPairPoleStatement`,
  `CuspidalPairBoundaryNonvanishingStatement` and `CuspidalArchimedeanPairRegularityStatement`,
  of which this note records no proof.

Neither track of the program is complete.

## Flath's Example 2, the fieldwise modules and the archimedean exponent bounds

This section was checked on 17 November 2026 against Library
`70eba6bb71c0dfc732a95146e6f12219c3cc76ae`. Every theorem named below was checked to use only
`propext`, `Classical.choice` and `Quot.sound`.

### Real-place nonvanishing of standard modules

The four helper modules `InversePowerFourier` (`Langlands/Analysis/`),
`RealGramFunction`, `RealStandardBlockPolynomial` and
`RealStandardNontrivialProof` (`Langlands/Representation/Archimedean/`) prove the real-place
nonvanishing of standard modules used by the proof of `CuspidalArchimedeanStandardGenericStatement`.
They first appeared in the Library at commit `70eba6bb`.

### Flath 1979, §2, Example 2

`Langlands.FlathRestrictedTensorStatement`
(`Langlands/Representation/Smooth/Factorization/RestrictedTensorStatement.lean`)
is the conjunction of four clauses; the factor-uniqueness clause is proved as
`restrictedTensorFactorUniqueness` (`RestrictedTensorUniquenessProof.lean`). The other three
clauses and the conjunction are proved as follows (all files in
`Langlands/Representation/Smooth/Factorization/`):

| Target | Main theorem and route | Proof in the Library |
| --- | --- | --- |
| `RestrictedTensorReferenceIndependenceStatement` | `restrictedTensorReferenceIndependence`: rescaling the reference vectors on the fixed lines, with the Library's `RestrictedTensor.congr` and `map_intertwines` | `RestrictedTensorReferenceIndependenceProof.lean` |
| `RestrictedTensorIrreducibilityStatement` | `restrictedTensorIrreducibility`: local ⇒ global through finite stages and the Library's `FiniteTensor.isIrreducible_external` with admissible Schur; global ⇒ local through the kernel of the map to the tensor with `V j` replaced by `V j ⧸ W`. Helper module `RestrictedTensor.StageAction` | `RestrictedTensorIrreducibilityProof.lean` |
| `RestrictedTensorAdmissibilityStatement` | `restrictedTensorAdmissibility`: an open subgroup contains a product of local open subgroups (trivial up to `H i` off a finite set), and its fixed vectors lie in a finite stage (`FiniteTensor.fixedVectors_external_le`). Same helper module | `RestrictedTensorAdmissibilityProof.lean` |
| `FlathRestrictedTensorStatement` | `flathRestrictedTensor`: the conjunction | `FlathRestrictedTensorProof.lean` |

### Fieldwise modules and cuspidal-support uniqueness

The fieldwise additions used by the routes to Jacquet–Shalika rigidity, GH Theorem 11.7.2 and
GH Theorem 10.7.2 are separate modules over `ContragredientUniqueness` and
`CuspidalPairAbsoluteConvergenceProof`:
`Langlands.Automorphic.RealizationEquivalenceTransport`, which is in the Library
(`Langlands/Automorphic/RealizationEquivalenceTransport.lean`), and
`Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceFieldwise`, which is not.

For `CuspidalSupportUniquenessStatement`, a route discharges the local-component hypothesis of
the reduction with `localComponentExistence`; its remaining inputs are
`IrreducibleSubquotientAdmissibilityStatement` and `CuspidalInducingDataRigidityStatement`.
The theorem `cuspidalSupportUniqueness_of_admissibility_rigidity` of that route is not in the
Library; the Library has `cuspidalSupportUniqueness_of_rigidity`
(`Langlands/Global/Factors/CuspidalSupportUniquenessReduction.lean`). The Library proves
`IrreducibleSubquotientAdmissibilityStatement`, as `irreducibleSubquotientAdmissibility`
(`Langlands/Automorphic/IrreducibleSubquotientAdmissibilityProof.lean`); this note records no
proof of `CuspidalInducingDataRigidityStatement` or of `CuspidalSupportUniquenessStatement`.

### The archimedean exponent bounds

In `Langlands/Representation/Archimedean/UnitaryGenericPairRegularityStatement.lean`
the right half-plane regularity of real and complex pair `L`-factors and both
reductions are proved in the Library. The remaining inputs of the
archimedean case of Getz–Hahn Theorem 11.5.2 were
`RealUnitaryGenericExponentBoundStatement` and
`ComplexUnitaryGenericExponentBoundStatement` (`|Re t| < 1/2` for the blocks of
a standard parameter of a generic unitarizable module), with the route of
the statement Markdown (Badulescu–Renard 2010, Theorems 8.1 and 8.2). Both are proved, as
`realUnitaryGenericExponentBound`
(`Langlands/Representation/Archimedean/RealUnitaryGenericExponentBoundProof.lean`) and
`complexUnitaryGenericExponentBound`
(`Langlands/Representation/Archimedean/ComplexUnitaryGenericExponentBoundProof.lean`).
The Library's `cuspidalArchimedeanPairRegularityReduction` derives
the archimedean pair regularity (`CuspidalArchimedeanPairRegularityStatement`) from these two
bounds (through the proved reductions), `archimedeanStandardAdmissible`,
`cuspidalArchimedeanStandardUnitarizable`, the genericity statement
`CuspidalArchimedeanStandardGenericStatement` and the irreducibility of archimedean standard
modules (`CuspidalArchimedeanStandardIrreducibleStatement`); the last two are proved as well
(above and next section). This note records no theorem that proves
`CuspidalArchimedeanPairRegularityStatement` itself.

This note records no proof of the other L4 inputs, `CuspidalPairPoleStatement` and
`CuspidalPairBoundaryNonvanishingStatement`. Neither
track of the program is complete.

## Archimedean irreducibility, self-pair continuation, the pole reduction and spectral decomposition

The following results were checked on 20 November 2026 against Library `7ae0d83b7cb2ad9aaca52ada487b3a5d3314323a`.
The third column gives the commit at which each first appeared in the Library.

| Track | Declaration(s) and module | First appeared at Library commit | Scope |
| --- | --- | --- | --- |
| L4 | `Langlands.Automorphic.cuspidalArchimedeanStandardIrreducible`, `Langlands.Automorphic.CuspidalArchimedeanComponentIrreducibleProof` | `5f5d3a914cd43b9dc1cd32c07887a973f561df96` | Exact proof of `CuspidalArchimedeanStandardIrreducibleStatement` for both real and complex place parameters in Getz–Hahn §11.4, (11.14)–(11.17). It uses isotypy and a compact multiplicity-one witness, not the generic exponent bounds. |
| L4 | `Langlands.Global.cuspidalSelfPairContinuation`, `Langlands.Global.Factors.CuspidalSelfPairContinuationProof` | `95d37e11bd46972d484c6fc9e6b864ff7625cf9e` | Exact proof of the partial self-pair continuation target from Jacquet–Shalika I, Lemma (5.2), pp.554–555. For the specified contragredient and unitary central character it also supplies absolute product convergence throughout `Re s > 1`. The positive global integral, bilateral Landau theorem and nonnegative logarithmic series replace the reduction from `CuspidalPairPoleStatement` (route B above). |
| L4 | `Langlands.Global.CuspidalPairPoleReductionStatement`, with new premise definitions for slab pairing, semi-local ratios and strip bounds | `95d37e11bd46972d484c6fc9e6b864ff7625cf9e` | Proposition definitions, not an exact proof. For Getz–Hahn 11.7.1 (Cogdell 2004 §4, pp.219–222) the four premises are `CuspidalArchimedeanParameterExistenceStatement`, `RankinSelbergGlobal.CuspidalSlabPairingStatement`, `CuspidalPairSemilocalRatioStatement` and `CuspidalPairVerticalStripStatement`. The archimedean existence premise, for both real and complex places, is proved, as `cuspidalArchimedeanParameterExistence` (`Langlands/Global/Factors/CuspidalArchimedeanParameterExistenceProof.lean`); `cuspidalArchimedeanParameterExistenceTC` covers totally complex fields only. The implication is distinct from Cogdell's direct route to `CuspidalPairPoleStatement`. This note records no proof of it (`cuspidalPairPoleReduction` proves the different `Langlands.Global.CuspidalPairPoles.CuspidalPairPoleReductionStatement`). |
| L3 | `Langlands.Global.standardParabolicSpectrumFiniteness`, `Langlands.Global.AdelicStandardParabolicFiniteness` | `95d37e11bd46972d484c6fc9e6b864ff7625cf9e` | The finiteness part of Getz–Hahn 10.5.1, conditional on equality of spectra for associate presented standard parabolics. Uses rational parabolic classification and Levi conjugacy. |
| L3 | `Langlands.Global.spectralDecomposition_of_reduction`, `Langlands.Global.AdelicSpectralDecompositionReduction` | `95d37e11bd46972d484c6fc9e6b864ff7625cf9e` | Proves Getz–Hahn 10.5.1 assuming `RelativeWavePacketOrthogonalityStatement`, `RelativeWavePacketAssociationStatement`, `RelativeWavePacketCompletenessStatement` and `GroupParabolicSpectrumStatement`. This note records no proof of any of the four inputs. |

For the archimedean pair regularity (`CuspidalArchimedeanPairRegularityStatement`), the
irreducibility statement above is a proved input, and so is genericity: the exact proof
`Langlands.Automorphic.cuspidalArchimedeanStandardGeneric`
(`Langlands/Automorphic/CuspidalArchimedeanStandardGenericProof.lean`) first appeared at Library
commit `95d37e11bd46972d484c6fc9e6b864ff7625cf9e`. It proves genericity for supplied real and
complex place parameters, not their existence. The real and complex exponent bounds are
`RealUnitaryGenericExponentBoundStatement` and `ComplexUnitaryGenericExponentBoundStatement`
(previous section). The full pole and strip statement is `CuspidalPairPoleStatement`, and the
global boundary nonvanishing statement is `CuspidalPairBoundaryNonvanishingStatement`. Neither
the conditional pole statements nor the self-pair proof replaces them.

For Getz–Hahn Theorem 10.5.1 (`SpectralDecompositionStatement`), the orthogonality and
completeness inputs need the
passage from the full rational quotient of Lapid Proposition 2 and Delorme
Theorem 7.9 to the split-centre quotient of Getz–Hahn §10.5, pp.281–282. The
paired reduction Markdown explains the required central twist and product
wave-packet factorization; its proof does not implement them. Pullback of a
centre-invariant function on `[G]` alone does not give an `L²` function on the
full quotient when the split-centre factor has infinite Haar measure.
Neither program track is complete.

### Further L3 and L4 results, checked at `b0a10aa9`

For L3, the [Arthur foundations ledger](arthur-l3-foundations-coverage.md)
records the five construction and statement modules of Arthur's parabolic combinatorics,
`(G, M)`-families and truncation, the exact comparison, `(G, M)`-family and truncation targets,
and the remaining analytic scope. In particular, the actual
parabolic spaces and truncation are not replaced by a second abstract
model; the abstract combinatorial lemma is proved, while the actual
height comparison, truncation estimates and proper-field descent are
separate statements.

For L4, the Library has
[`Langlands.Global.cuspidalPairBoundaryNonvanishingReduction`](../../Langlands/Global/Factors/CuspidalPairBoundaryNonvanishingReduction.md),
which first appeared at Library commit
`95d37e11bd46972d484c6fc9e6b864ff7625cf9e`. It proves the implication
from `CuspidalPairBoundaryNonvanishingEnlargedStatement`: for each admissible
finite omitted set `S`, the premise gives one meromorphic Euler-product
representative for a superset `S₀` with nonpositive order on `Re s = 1`.
Restoring the finitely many omitted reciprocal-polynomial factors cannot
increase the order; uniqueness of the continued product gives the statement
for every representative outside `S`. This implements the set-of-places
passage in Shahidi 1981, Theorems 5.1–5.2, pp.351–353. It does **not** prove
the enlarged-set premise (for which the Library has only the conditional
`cuspidalPairBoundaryNonvanishingEnlarged_of_eisenstein`,
`Langlands/Global/Factors/CuspidalPairEisensteinDerivation.lean`), the holomorphy of the
corresponding generic Eisenstein coefficient, or the full nonvanishing target; this note
records no proof of these. They are analytic inputs for L4 and the H3 factor comparison.
