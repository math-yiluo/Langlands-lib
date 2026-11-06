# Global automorphic library and Henniart inputs: coverage and assumptions

This is the initial coverage ledger for standing program
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1, checked on
2 November 2026 against Library `545ccb3366b363dc0fe0a6d000b281a88d7c2407`.
The program has two required outputs: a general connected-reductive automorphic
library over number fields, and the global inputs of Henniart's 2000
local-correspondence construction. Neither track is complete.

The registered roadmap
[`henniart-global-automorphic-roadmap-2026-11-02`](</home/taskhub/pilot/literature/Global roadmap - Henniart local Langlands correspondence and a modern automorphic library (2 November 2026).md>),
SHA-256
`7be7def5b4039086928d7a9844c50fe5cea58513c24108191cef1ff239f4c8e3`,
and the program contract determine the planned coverage below. Planned source
locators are reading targets from that roadmap, not assertions that this ledger's
authors have read every original or that the corresponding theorem is formalized.
The receipt section separately identifies checked public results. The original
tables and nine receipt rows below are a historical snapshot at that Library
commit. The dated continuation at the end records later developments; it does
not recertify every historical status or executor assignment.

## How to read the status

“Public statement” means an independently accepted and integrated proposition
definition. It does not prove that proposition. “Public proof” below requires
both independent acceptance and publication, including exact-target machine
validation. An interface located in current source without an audited receipt is
identified as such and receives no acceptance credit here. Child publication,
drafts, source reading and shared-DAG entries are coordination evidence.

The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
Lean 4.34.0 and mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Worker 116 checked that the workspace's Lean files match the named Library.
The nine receipts listed below were fetched, their reviews and publication states
read, and their current pairs compared with the frozen pairs. The associated
factor Markdown has a separately reviewed later correction.

## One construction path

Algebraic-groups program `2b5e4a00-9d44-49a4-9c89-979fb5b6233e`
owns rational/Galois group structures, parabolics, Levis, unipotent groups,
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
growth hypotheses. Worker 2's `RationalInvariantFunctions` uses rational left
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
`AdeleQuotient F`. Its comparison with all rational parabolics remains an
obligation. Compact additive `A_F/F`, or compact norm-one idele classes, does not
prove finite covolume of an adelic reductive quotient.

## Library track

The sources in this table are planned original-source obligations unless a
checked receipt below supplies a narrower public result. “Parent” means
Workers 116 and 84 under the standing program; it is not a newly delegated task.

| Block | Required source correspondence | Current interface and proof boundary | Responsible work |
| --- | --- | --- | --- |
| L1: quotients and spaces | GH (2.20), Chapters 2 and 9; applicable reduction theory and MW95 I–II | Construct actual `[G]`, quotient measures, Siegel sets, finite volume, smooth/finite-level/archimedean spaces, uniform moderate growth, constant terms and cusp forms. Existing additive quotient and GL_n function objects are reuse inputs; no general-reductive completion is credited here. | Child `7d827a3e-4245-4c06-ad81-48f413c26faf`, Workers 94 and 112, claimed revision 1. Adelic-points candidate `ace67c65-f5f1-4584-a1af-8993cc50c49b` has machine validation, with semantic review and publication pending; it constructs coefficient points and GL_n principal-map comparisons, not quotient analysis. |
| L1: cuspidal analysis | GH 9.1.2, 9.1.3 and §§9.2–9.5; 9.6.4, 9.6.5, 9.7.1, 9.7.3; MW95 I.2.12 for 9.7.1 | Closed cuspidal subspace, trace class, discrete decomposition with finite multiplicities, rapid decay and algebraic/Hilbert comparison remain required. The verified GL_n differential-growth proof is narrower: its growth constants can depend on derivative, form and finite slice. It does not establish uniform moderate growth or these spectral results. | Parent after the foundations exports; no exact targets or proofs claimed by this ledger. |
| L2: function-space meromorphy | BL §2.3, §§3.1–3.2 and Appendix A; MW95 I–II | Build the function-space topology and local common denominators, then actual Eisenstein and intertwining constructions. Pointwise scalar continuation is insufficient. | Parent, following L1; no candidate or proof credited here. |
| L2: continuation identities | BL Lemma 6.10 and Corollary 8.6; GH 10.2.3 and 10.3.2; source-qualified MW95 IV.1.8, IV.1.10 | Constant-term formulae, functional equations, cocycles/composition, root-hyperplane singularities and Fréchet continuation, with exact convergence and normalization hypotheses. Imaginary-axis holomorphy is a separate L3 result, not a conclusion assigned to BL alone. | Parent; eventual exact-target proof children after public statements. |
| L3: isometry and regularity | Lapid 2011 Proposition 2, Theorem 2, p.314, and Proposition 6, pp.329–330; its Working Hypothesis p.312 | Arthur truncation, Langlands' combinatorial lemma, `(G,M)`-families, Schwartz estimates and direct integrals must be constructed. Prove L² wave packets, the Weyl-compatible isometry with weight `\|P(M_P)\|⁻¹`, imaginary-axis holomorphy and source-qualified unitarity. | Parent after L2; no public implementation credited here. |
| L3: completeness | Delorme 2023 Theorem 7.9, p.33; GH 10.5.1, (10.22)–(10.24) | Surjectivity requires BL/Lapid and explicit accounts of Lapid 2013, Bernstein Plancherel support and Franke temperedness. Inducing data range over the discrete spectrum, not only cuspidal data. The actual unitary transform remains required. | Parent; no proof credited here. |
| L4: inducing data and isobaric objects | GH 10.7.2, JS-II 4.4; GH 10.7.5–10.7.6 | The checked `CuspidalSpectralRigidityStatement` supplies mixed-rank trace independence and numerical recovery as unproved propositions. It supplies no general induced/isobaric realization bridge. Isobaric sums require the correct irreducible quotients; arbitrary automorphic subquotients of cuspidal induction are not all isobaric. | Existing statement task `91266440-3276-48dc-ab77-8d1c1fa386e8`, Workers 35/44, retains its units; parent supplies common-library analytic proofs and comparisons. |
| L4: Whittaker and multiplicity | GH 11.3.6, 11.4.3; GH's general-rank citation to Cogdell 2007 | Whittaker expansion and cuspidal multiplicity one remain required. The roadmap records Cogdell 2007 as missing; acquire and register it before relying on it. | Parent with current Whittaker/local owners; no general-rank proof credited here. |
| L4: pair factors and global analysis | GH 11.5.2, 11.7.1; JPSS; Shahidi 1981 Theorem 4.1; Jacquet 2009 for archimedean theory | Local unitary regularity and global continuation, poles, functional equation and growth remain distinct obligations. The roadmap also records Barthel–Ramakrishnan 1994 as missing. No Ramanujan hypothesis is silently imposed. | Parent with actual local-factor owners; H1 may use individually explicit hypotheses meanwhile. |
| L4: rigidity and pole detection | GH 11.7.2–11.7.3, JS-I 4.8; Shahidi 1981 Theorem 5.2, p.353; GH 11.8.1 | Strong multiplicity one retains almost-all-place equality. Partial pair L-function nonvanishing on `Re(s)=1` is a required global theorem; local GH 11.5.2 does not replace it. Pole counting needs omitted-factor holomorphy and nonvanishing. | Parent; not supplied by the checked JS-II statement receipt or by spectral completeness alone. |

The optional MW89 GL_n residual-spectrum classification is separate.
Spectral completeness by itself neither classifies the discrete inducing data
nor constructs a trace formula.

The actual normalized idelic absolute value is already available in
`Langlands.Global.IdeleAbsoluteValue`. Worker 112 located this reuse input;
Worker 116 checked its accepted-public construction receipt and the current
pair below. In particular, `full_diagonalUnits` proves the normalized product
formula for actual principal ideles, and `ideleClass` descends the continuous
character to the actual principal quotient. Identification with Haar moduli,
parabolic determinant characters and relative norms remains separate. The
roadmap's observation that the formula is absent from the pinned mathlib must
not be read as a claim that no project construction exists.

## Henniart track

| Block | Source correspondence | Current declaration or construction boundary | Responsible work |
| --- | --- | --- | --- |
| H1: finite-place comparison | Henniart 1986 Theorem 4.1 and §4.3; Henniart 2000 §§2.3–2.8 | The finite-exceptional-set engine must compare actual meromorphic factors using one finite set containing infinity and all bad places. Cancellation must be proved at every auxiliary place after highly ramified twists. Nonzero factors and factor/measure existence cannot be omitted. | Child `205503d3-82c7-4b1a-a4f0-90d02bbe9a2e`, Workers 64/352, claimed revision 1. Statement candidates `dbfdb723-00fa-40c0-8d64-d8987a6f2517` and `3b672bcc-5b63-416b-b26c-cc7cff7359e7` are staged; neither supplies a public proof. Worker 352 handles finite-S meromorphic comparison; Worker 64 handles factor adapters and pole/pairing arguments. |
| H1: polynomial separation | Henniart 1986 Lemma 4.4, printed p.159/PDF16; reciprocal-radius criterion is derived content | `Langlands.Global.GammaSeparationStatement` in `Langlands.Global.Factors.SeparationStatement` is the conjunction of `GammaPolynomialSeparationStatement` and `ReflectedRootRegionStatement`. Its separate four-polynomial target is not the already proved two-polynomial reflection lemma. | Exact proof child `845cd013-e744-4bd2-8eb0-a928bbc72b6a`, Worker 468, revision 1. Proof candidate `12080b7e-a02c-4e98-952a-5ac227200136` passed exact-target machine validation; independent review and publication remain pending. H1 retains the actual-factor adapter obligations. |
| H1: pairing and poles | Henniart 2000 §§2.5–2.8 and Appendix; Shahidi 1981 Theorem 5.2 | Preserve rank, unitarity/temperedness, finite support and degree/positivity conditions. Pairing/isometry and pole orders remain conditional on genuine analytic inputs until L4 discharges them. | H1 with the existing virtual-lattice/pairing branch `62ea68fa-e1f4-4187-811b-7436743bba6a`; exact overlapping exports are still being coordinated. |
| H2: arithmetic and characters | Henniart 2000 §§3.3–3.7; Henniart 1984 Lemma 3.6; Artin–Tate X.2 Theorem 5; Harris 1998 Lemma 4.7 | The detailed source-to-target table below preserves the different field, character, stabilizer, tower and normalization obligations. CM and general-position statement publications are verified; no H2 existence proof is credited. | Worker 84 audits H2 and coordinates construction work with existing owners; the parent records accepted-public exports here. |
| H3: global construction and factors | Henniart 2000 global construction and §§2.3–2.8; Henniart 2001 §§5.5–5.12 and §7.3 for the qualified variants | Assemble actual realizations, weak association, local maps and factor objects on individually stated deep hypotheses. The checked `Langlands.ClassField.Global.RelativeWeilGroup.AssociatedFactorStatement` is a finite-place, relative-Weil, cuspidal statement family, not a proved complete global-to-local theorem. | Parent after H1/H2; current global statement owners remain Workers 35/44. No H3 assembly proof credited here. |
| H4: discharge | Arthur–Clozel III.3.1, III.4.2, III.5.1, III.6.2; HH95; Clozel/Clozel–Labesse/Kottwitz and the separate Harris/Shimura chain | Keep transfer and geometry as explicit sourced hypotheses in H3 until independently proved. Trace-formula and geometric Galois-existence work are long-term obligations, separate from the modern spectral-completeness theorem. | Parent coordinates existing algebraic, representation, class-field, Shimura and Harris owners; no discharge claimed. |

### H2 source-to-target detail

Worker 84 supplied the following audited rows and direct-reading bounds.
Unqualified declaration names in this subsection have prefix
`Langlands.Global`. His recovery check
`b031bf25-0032-402e-8e59-493ce402c884` compiled the five arithmetic
statement modules without diagnostics. Worker 116 independently checked the
current CM and general-position pairs against their accepted-public receipts;
the other rows disclose their narrower evidence. Compilation records declaration
availability, not the truth of these propositions.

| Block and original passage | Current target declarations and scope | Remaining construction/proof obligation | Owner/disposition |
| --- | --- | --- | --- |
| Totally-real realization: Henniart 2000 §3.3 p.449; Henniart 1984 Lemma 3.6 pp.34–35 | `TotallyRealGaloisRealizationStatement.{u,v}` in `Arithmetic.FieldRealizationStatement`: arbitrary-universe p-adic fields, totally-real number fields, full global/local Galois-group comparison, unique place, compatible continuous completion equivalences. `SplitAuxiliaryQuadraticsStatement.{u}`: real and imaginary quadratics split at p, with disjointness from the supplied totally-real field. Aggregate `FieldRealizationStatement`. | Actual weak approximation/Krasner realization and totally-real strengthening; actual split quadratic construction. These targets do not construct the later CM composita, intermediate-field tower or paired completion data. | Existing statements: Worker 35, task `91266440-3276-48dc-ab77-8d1c1fa386e8`. Current declarations compile; historical artifact `09484640-24a9-4eb6-afee-e258a67ebc71` is unresolved (`NOT_FOUND`), so no recovered receipt is asserted. Actual field constructions remain with Worker 2. |
| Finite-order prescription and twist isolation: Artin–Tate X.2 Theorem 5 p.80; Henniart 1986 Proposition 3.4/§4.3 | `FiniteOrderCharacterPrescriptionStatement.{u}`, `LocalCharactersArbitrarilyRamifiedStatement.{u}`, `RamifiedTwistIsolationStatement.{u}` in `Arithmetic.CharacterPrescriptionStatement`. Actual idele-class characters and completion units; unrestricted order bound **2n**, whole archimedean factor, arbitrary nontriviality on `1 + m^r`, disjoint selected/ramified sets, trivial infinity component for isolation. | Grunwald–Wang and local finite-order character/depth construction; assembly with a common finite order. No claim of order n without the Wang compatibility condition. H1 consumes isolation but does not thereby prove its arithmetic input. | Worker 35 statements retained. Historical short reference `7319298c` is navigation only; no exact recovered receipt or current proof task confirmed. Local reciprocity ownership remains with Worker 4. |
| CM Lemma 1: Henniart 2000 §3.5 p.450 | `CMUnramifiedInfinityRealizationStatement.{u}` in `Arithmetic.CMCharacterStatement`: anticyclotomic integral infinity type, **one common positive scaling**, actual complex conjugation, conjugate self-duality and unramifiedness at every finite place. Current scope is any CM field, generalizing the source's chosen quadratic setup. | Class-group/unit/norm-quotient construction and finite-obstruction killing. No theorem is supplied by the statement publication. | Worker 35 statement artifact `9add3b08-2bb2-4580-b833-18fb3b247063`, fetched accepted/public under `lean.statement@1`, publication `fe68653a42ed5ae0a2d7f5cef0697a68e8acc978`, Reviewer 29. |
| CM Lemmas 2–3: Henniart 2000 §3.6 pp.450–451 | `CMFiniteCharacterPrescriptionStatement.{u}`, `IntegralUnitCharacterExtensionStatement.{u}`, `CMRegularUnitPrescriptionStatement.{u,v}`; aggregate `CMCharacterGlobalizationStatement`. Finite selected places are disjoint from their conjugates; full finite-order local prescription is the Lemma 2 target. The final regular Lemma 3 target prescribes **integral units only**, with distinct weights above an imaginary-quadratic embedding and the same positive scaling. | Extend integral-unit characters to finite-order local characters; prescribe at selected and conjugate places; form the conjugate quotient; combine with unramified infinity realization. Uniformizer values must remain free in the final target. Central-character and Harris-normalization conclusions still require explicit comparisons. | Same accepted-public CM statement artifact; four component assertions, no component proof. Coordinate existing targets with Worker 35 before proof children. |
| Auxiliary norm stabilizer: Henniart 2000 §3.4(3); Harris 1998 proof of Lemma 4.7 pp.204–206, (4.12)–(4.13) | `HasExactUnitNormStabilizer`, `AuxiliaryCharacterStatement.{u,v}` in `Arithmetic.AuxiliaryCharacterStatement`. Actual determinant norm, Galois action, exact stabilizer **on valuation units**, arbitrary depth and all primes including 2. | Normal-basis logarithmic-lattice character construction, finite-order reduction, exactness and depth. Harris's literal embedding `(Z/2^N Z)ˣ → Cˣ` is unavailable for N ≥ 3. A sufficiently deep cyclic principal-unit construction is a proposed repair, not a proved replacement; `1+2Z₂` itself has torsion. | Worker 35 statements retained; historical short reference `68769040` does not supply a recovered receipt. No auxiliary proof owner/task confirmed. |
| General position: Harris 1998 Definition 4.5 and Lemma 4.7 p.201, proof pp.204–206; Serre IV §2 pp.67–68 for solvable local Galois groups | `GeneralPositionOfExactStabilizerStatement.{uF}`, `ExactStabilizerCharacterStatement.{uF}`, `GeneralPositionCharacterStatement.{uF}`; aggregate `HarrisGeneralPositionStatement` in `Arithmetic.GeneralPositionStatement`. `GeneralPosition.IsInGeneralPosition` uses actual Weil subgroups, finite-index Mackey constituents and a cyclic-prime tower from the normal closure. | Separate unit-norm-to-Weil stabilizer transport and conductor/depth comparison, Clifford–Mackey irreducibility, and actual solvable-group/fixed-field tower. Existence of a normalized reciprocity family is a separate obligation: these targets quantify over a supplied normalized family. | Worker 35 statement artifact `a3d0ff03-3838-47e6-87ba-b6ca99a299e3`, fetched accepted/public under `lean.statement@1`, publication `9a1bc5f8b8379aa4fe176f3af65ec4c9d96fc715`. No proof acceptance is asserted. |
| CM/tower and H3 adapter: Henniart 2000 §§3.3–3.4, 3.7; corrected Harris setup | Existing `Harris.PlaceDatum`, `Harris.PlaceDatum.IsCompatible`, `Harris.PlaceDatum.HasComponent`, `Harris.IsRelativelyRegular`, `Harris.IsAlgebraicAfterTwist`, `Harris.IsProposition48Datum` in `Arithmetic.HarrisSetup`. | Construct actual CM composita/towers and compatible places/completions, then compare local components and infinity types. CM regular integral weights alone do not produce Harris's full local prescription or `IsAlgebraicAfterTwist ([E':E]-1)`. Retain the half-norm parity correction when intermediate ranks change. | Worker 35 owns Harris setup/statements; Worker 2 owns actual global constructions; Worker 50 owns completion/adelic functoriality. Worker 44 reports no own pending H2 revisions or proofs. These are ownership boundaries, not delegations or waived prerequisites. |
| Brauer/rank-one route: Henniart 2000 §3.7 and global functional equations | Consume existing virtual-representation, rank-one local-constant and arithmetic functional-equation objects; no parallel object family proposed here. | Actual Brauer/induction identities and factor adapters, preserving auxiliary local cancellation and central characters. The H2 rows above do not discharge these identities or deep transfer/geometry. | Coordinate with task `62ea68fa-e1f4-4187-811b-7436743bba6a` and existing arithmetic/local-constant owners; exact child scope remains to be agreed. |

Worker 84 directly read Henniart 2000 pp.448–451 (PDF 10–13), including
§§3.1–3.8 and the printed Lemmas 1–3 proofs; Henniart 1984 Lemma 3.6
pp.34–35 (PDF 35–36); Artin–Tate X.2 pp.78–81 (PDF 87–90), including
Theorem 5's proof; Harris 1998 pp.204–206 (PDF 28–30) and its TeX proof
lines 1740–1824; and Serre IV §2 pp.67–68 (PDF 74–75). Other H2
locators are inherited from paired statement documentation unless they fall in
these ranges. This attributes Worker 84's reading; it does not assert reading
of those complete sources by Worker 116.

Registered sources are `henniart-2000-simple-proof`,
`henniart-1984-gl3`, `artin-tate-2009-class-field-theory`,
`harris-1998-local-langlands` and `serre-1979-local-fields`.
The total-reality strengthening is attributed to Henniart 2000 §3.3, rather
than asserted verbatim in Henniart 1984 Lemma 3.6. Harris's source-folder
`CORRECTION_SOURCE.md` describes corrections to Harris 1997 contained in the
1998 article; it does not establish an erratum to Harris 1998. The all-primes
auxiliary-character construction, including the `p=2` repair, remains open.
Shared arithmetic drafts supply navigation rather than acceptance evidence.

## Checked accepted-public reuse

All artifact IDs in this section name exact historical receipts, not Lean
imports. Import the present declarations by module name. The review and
publication data were read from TaskHub; current pair hashes were compared
against Library `545ccb3366b363dc0fe0a6d000b281a88d7c2407`.

| Result and exact current interface | Accepted/public evidence | Scope retained |
| --- | --- | --- |
| `Langlands.Global.IdeleAbsoluteValue.full` and `ideleClass` in [`IdeleAbsoluteValue.lean`](../../Langlands/Global/IdeleAbsoluteValue.lean) | Construction `22484bf5-be00-4a0b-8c49-12b1b615fc8f`, policy `lean.definition@1`; task `6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`; Reviewer 7269, review `f790311f8cdb4b9499435bbd7f3ae413`; validation `b05a0cae-64ca-44e0-ac1b-5cfc88d61cd9`; publication `00315d47b3cf847fb5aa4184c78df11887f7fe20`. | Genuine normalized finite/infinite/full continuous idele characters, principal triviality `full_diagonalUnits`, quotient descent and local restrictions. This is a construction publication, not a separately targeted `lean.proof@1` receipt; no Haar-modulus, relative-norm or automorphic-existence comparison is supplied. |
| `Langlands.Global.CMCharacterGlobalizationStatement` in [`CMCharacterStatement.lean`](../../Langlands/Global/Arithmetic/CMCharacterStatement.lean) | Statement `9add3b08-2bb2-4580-b833-18fb3b247063`; task `91266440-3276-48dc-ab77-8d1c1fa386e8`; Reviewer 29, review `4f9ad561d945484a833dc32047a426ae`; validation `c5330718-63a3-421c-be49-d508aef31a78`; publication `fe68653a42ed5ae0a2d7f5cef0697a68e8acc978`. | Four unproved propositions generalizing Henniart 2000 Lemmas 1–3 to arbitrary CM fields and finite conjugate-separated sets, retaining common positive scaling and final integral-unit prescriptions. Auxiliary exact stabilizers and completion/Harris adapters remain separate. |
| `Langlands.Global.HarrisGeneralPositionStatement` in [`GeneralPositionStatement.lean`](../../Langlands/Global/Arithmetic/GeneralPositionStatement.lean) | Statement `a3d0ff03-3838-47e6-87ba-b6ca99a299e3`; same statement-owner task; Reviewer 443, review `751d1130928947f9afc958c978084c4f`; validation `08cf6388-2a3c-4dcc-a33c-dccd0650b2d3`; publication `9a1bc5f8b8379aa4fe176f3af65ec4c9d96fc715`. | Concrete Weil subgroups, Mackey constituents and normal-closure tower; supplied normalized reciprocity remains a hypothesis. Residue characteristic 2 is included in the statements, with the cited construction gap retained. No existence or implication-between-targets proof is supplied. |
| `Langlands.Automorphic.automorphicDifferentialGrowth` in [`DifferentialGrowthProof.lean`](../../Langlands/Automorphic/DifferentialGrowthProof.lean), proving `AutomorphicDifferentialGrowthStatement` | Proof `d64c9a81-078b-43c0-885e-4f7bb3a52634`; task `e0d3fab3-d5c8-47ae-bd65-d85037d6fd80`; Reviewer 6418, review `c103bf3467e94694af6ec6d4ff826c72`; exact-target validation `8972152f-ba24-41ae-a076-f74f1a2142d2`; publication `8f53f05bb76983088fd64f190658c6ac4c3edc1b`. | Genuine GL_n enveloping action, arbitrary number field and every natural rank, with bounds separately on finite slices. Does not prove general-reductive uniform moderate growth or spectral existence. |
| `Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement` in [`CuspidalSpectralRigidityStatement.lean`](../../Langlands/Automorphic/Unramified/CuspidalSpectralRigidityStatement.lean) | Statement `657004fa-26b2-4972-b3bf-f8c75b4fc0aa`; task `91266440-3276-48dc-ab77-8d1c1fa386e8`; Reviewer 2387, review `3927186840964c5b8633710bce519010`; validation `c174dcab-b683-4bc7-90ad-c0a9b42f1e34`; publication `0123ad79ddfe032cfbdceb25fbf4cf3dbf574612`. | JS-II printed pp.805–809, Theorem 4.2 and numerical recovery in Theorem 4.4. Actual full cuspidal classes, supplied genuine presentations, mixed positive ranks, repetitions and one finite exception set. Analytic independence/recovery proofs, presentation existence/uniqueness and induced/isobaric realization remain open. |
| `Langlands.Automorphic.Unramified.CyclicCuspidalFiberStatement` in [`CyclicCuspidalFiberStatement.lean`](../../Langlands/Automorphic/Unramified/CyclicCuspidalFiberStatement.lean) | Statement `36f3623e-aaaa-4237-9f0a-8cd8948e3551`; same statement-owner task; Reviewer 3335, review `3f1f4cf32de946cfb90280ee517f9df5`; validation `a39958c9-a1f0-4ee2-bef7-a7d332b40b04`; publication `9de4c69288df556276e9782428eda52c7ee37341`. | AC89 III.3.1, printed pp.199–201: cyclic extension, same positive rank, actual norm-trivial finite-order twist, all places above and residue-degree powers. The common-upstairs consequence assumes the analytic proposition; no lifting/descent proof follows. |
| `Langlands.ClassField.Global.RelativeWeilGroup.AssociatedFactorStatement` in [`AssociatedFactorStatement.lean`](../../Langlands/Automorphic/AssociatedFactorStatement.lean) | Original statement `f985627e-9f59-41f6-802f-a9c3215838b7`; Reviewer 3172, review `442281cacae3486e94c02975c10e1966`; validation `780311f4-c0f2-454e-bbf2-0f68513baeff`; publication `efef3e8dad656737d40a56704c6373cf894d3cbd`. | Henniart 2000 §§2.3–2.4, printed pp.444–445; Henniart 1986 Theorem 4.1, Lemma 4.4 and Proposition 4.5, pp.157–160. Four unproved propositions with the qualifications below. |
| Current [`AssociatedFactorStatement.md`](../../Langlands/Automorphic/AssociatedFactorStatement.md) correction | Documentation correction `fe26cded-c80e-4f7f-ab92-0bf6d5083cd8`; task `243040f2-ce4e-44b3-b3b0-11b9ac33e3f7`; Reviewer 4616, review `60f112931e624da28cc4872772008a90`; validation `d675e7c5-400b-4c4c-8371-fed39b8dca48`; publication `bc8de2287e5c24972c55277b2aa9611523dfc5dc`. | Lean unchanged. The corrected prose acknowledges conditional existential claims for measures, common factors and inducing blocks; it does not claim witnesses were constructed or propositions proved. Current Lean matches the original; current Markdown matches this correction. |
| `Langlands.RankinSelberg.reflectionRigidity` in [`ReflectionRigidityProof.lean`](../../Langlands/Representation/RankinSelberg/ReflectionRigidityProof.lean), proving `ReflectionRigidityStatement` | Proof `aec1db14-98dd-4baa-b732-30bf3551bdac`; task `994cc755-0c12-4cfa-9e30-ff2ff952e741`; Reviewer 2264, review `dbd1a0139f774da6858d9d569008ea22`; exact-target validation `eb4ac78d-e6c2-47a2-9809-edf46c1fef29`; publication `84f5d5a32df09643d499627f7ca72504805d3365`. | Internal two-polynomial reciprocal-reflection rigidity with a strict radius gap, normalized polynomials, arbitrary integer monomial exponent and complex unit. Reuse with rational-evaluation infrastructure; it is not a proof of the four-polynomial GammaSeparation conjunction. |

The associated-factor conjunction comprises `AssociatedGammaStatement`,
`AssociatedTemperedFactorStatement`, `AssociatedSupercuspidalInductionStatement`
and `AssociatedCuspidalFactorStatement`, all in
`Langlands.ClassField.Global.RelativeWeilGroup`. Its retained limits are:

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

These are disclosed scope differences of a partial statement contribution,
not discharged construction or analytic obligations.

## Deep hypotheses and their discharge

| Input allowed explicitly in a conditional H3 theorem | Eventual discharge route and boundary |
| --- | --- |
| Actual global Rankin–Selberg functional equations, analytic regularity, inducing-data rigidity and boundary nonvanishing | L1–L4 through the shared general library and proved GL_n comparisons. These are library-owned obligations, not permanently outsourced deep assumptions for program completion. |
| Highly ramified stability and actual local factor/measure, local-map and presentation existence | H1/H2 and existing local-factor, CFT and automorphic-definition owners. The finite-S engine must name each missing input, rather than turn absent factor objects into vacuous implications. |
| AC89 III.3.1 twists | Checked public statement above; analytic proof still an explicit hypothesis. |
| AC89 III.4.2(a–f) lifting/descent, III.5.1 local base-change compatibility, III.6.2–4 automorphic induction | Existing Workers 35/44 statement scope; H4 trace-formula discharge remains open. Almost-all Hecke-eigenvalue induction does not imply ramified compatibility. |
| HH95 ramified functoriality | Separate sourced input where actually used; do not infer it from weak association or insert LLC-dependent compatibility into its own proof. |
| Weak geometric Galois existence, He2001 §5.5 | Coordinate Clozel/Clozel–Labesse/Kottwitz with the Shimura owners. Retain `F = F⁺ I`, conjugate self-duality, regular algebraicity, and a discrete-series place split in `I`. Output is semisimple of dimension `a*n`, `a ≥ 1`, and the almost-everywhere shifted L identity has power `a`; no `a = 1` assumption. |
| Harris non-Galois induction and cohomology | Separate Harris/Shimura chain, following He2001 §§5.6–5.12, Taylor's corrections and the [current audit](../henniart/audit.md) and [Harris note](../henniart/harris-1999.md). The located `Langlands.Global.Harris.Proposition48Statement` is not credited here as a proof. |

Numerical surjectivity (Henniart 1988), epsilon characterization (1993),
extension to all representations and equal characteristic remain outside this
program's global-input conclusions. Henniart 2001's embedding-problem variant
is not an explicit description.

## Ownership and Task 0 consumers

Existing definitions remain with Worker 2,
`6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`. Existing global statements,
including the outstanding transfer, rigidity and associated-factor units,
remain with Workers 35/44,
`91266440-3276-48dc-ab77-8d1c1fa386e8`. The general extension adds proved
comparisons rather than replacing these owners. Worker 35's existing
constant-term/operator pause is preserved; peer coordination does not lift it.
Algebraic structure remains with Workers 1107/207 under the algebraic-groups
program. Pairing and finite-witness coordination preserves
`62ea68fa-e1f4-4187-811b-7436743bba6a` and its virtual-lattice prerequisites.

| Task 0 node | Public interface presently available | Missing program output |
| --- | --- | --- |
| `proof.henniart-globalization` | Current-source field, character and general-position proposition families named in H2; actual weak-induction relation `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.IsWeakAutomorphicInductionOf` in `Langlands.Automorphic.WeakAutomorphicInduction`. No proved complete globalization interface is identified by this ledger. | H2 constructions/proofs and H3 assembly on individually named transfer and geometry hypotheses, preserving exact local, infinity and central-character requirements. |
| `proof.global-to-local-factors` | Checked public `AssociatedFactorStatement` and its four component targets; `GammaSeparationStatement` has a separately claimed exact proof child. The checked reflection theorem is a narrower reusable proof. | Proved H1 finite-S engine, separation and actual-factor adapters; L4 discharges global analytic hypotheses; H3 connects actual weak association and local components. |
| `proof.harris-global-input` | Existing Harris/Shimura statements and audited sources are separate navigation inputs. No unconditional Harris theorem is credited here. | Independent cohomological/geometric construction and corrected conditional comparisons; not implied by either node above. |

The ledger will acquire exact public targets and accepted-public proof receipts
as each focused unit is integrated. The newly delegated L1, H1 and GammaSeparation children have staged
candidates, with the specific validation boundaries recorded above. None is
credited as an accepted-public output at the inspection recorded here. The ledger itself supplies no mathematical completion evidence.

Prepared by Worker 116, using Worker 94's roadmap/program and initial block
contracts and Worker 84's detailed H2 source-to-target audit. Source correspondence
for the checked reused propositions/proofs follows their reviewed paired
Markdown; the wider tables remain explicit planning coverage.


## 2 November 2026 continuation snapshot

This continuation is checked against Library
`0ebc0efd383ff160084af3b33ab2b7806f7a1dde`. It preserves the original
snapshot above, including all nine historical receipt rows. Worker 116 inspected
the parent task and its candidates on recovery and recompiled both private proof
pairs. More detailed candidate fetches and peer reports are distinguished below.
Independent semantic approval while a candidate remains staged is not accepted
publication; none of the pending units in this continuation is credited as a
public result.

### General analysis and source work

The following five Worker 116 submissions have successful machine validation and
independent semantic approval. They remain staged and unpublished in the
inspected state.

| Focused unit | Candidate and independent review | Exact scope and remaining boundary |
| --- | --- | --- |
| Operator-ideal definitions | `8283e313-e66e-48a7-9b7a-117328293c44`; Reviewer 8708, review `2f7ad1a5-56cd-4cc4-8461-b1999ae01935` | `Langlands.Analysis.OperatorIdeals`, a general analytic prerequisite. Definition review does not supply the operator-ideal theorems or automorphic applications. |
| Hilbert–Schmidt basis independence statement | `4a7c53eb-5adb-4834-8c28-3c8e658221ec`; Reviewer 8726, review `e68e3f54-6701-44b7-8744-ad6230e6a22a` | `Langlands.Analysis.OperatorIdeals.HilbertSchmidtBasisIndependenceStatement`: rectangular bounded complex Hilbert operators, two independently indexed domain bases and four universe parameters; equivalent square summability and conditional equality of the squared sums. This is a disclosed derived extension of the separable endomorphism assertion in GH 9.1.1, not a published proof. |
| GH Chapter 9 source map | `b9333fd3-7dfc-40cc-8863-69a6d159dd23`; Reviewer 8732, review `bdb90666-9f34-48f6-b937-ab8cb5d0a249` | `notes/automorphic/getz-hahn-cuspidal-source-map.md`. Original-source and errata reading, analytic dependencies and retained boundaries; no Lean theorem publication. |
| MW95 cuspidal-decay source map | `9538810f-dc70-4b26-a113-ab069b259a0d`; Reviewer 8763, review `7ee33309-513c-4625-95c6-2dab05cf3de1` | `notes/automorphic/mw95-cuspidal-decay-source-map.md`, Workers 116/94. Records I.2.3, I.2.5, I.2.10–12 and I.2.17, including the central-growth and fixed-Siegel qualifications. Integration must preserve both this and the GH source-map link. |
| Fixed-exponent differential growth statement | `c4ad6835-a62d-4053-b10c-0574e7c83781`; Reviewer 8792, review `b0a1e600-974e-4122-92db-f3be94026134` | `Langlands.Global.ArchimedeanGL.FiniteUniformDifferentialGrowthStatement K n`, Workers 116/94: every natural rank, including zero, on the infinite-adelic GL_n group. For compact-finite, centre-finite smooth functions, each supplied growth bound with a nonnegative real constant and natural exponent is retained for every genuine enveloping derivative, allowing a new constant. This strengthens the derivative-dependent result; it does not prove the general adelic uniform-growth or cuspidal-decay obligations. |

Two complete private proof pairs are shared in parent draft revision 2. Recovery
checks `cd51adf5-9d79-4069-840d-e24a50f7427a` and
`7145f664-28c2-4953-b594-4304c5857afb` compiled respectively
`Langlands.Analysis.HilbertSchmidtBasisProof` and
`Langlands.Global.ArchimedeanFiniteUniformGrowthProof`, with zero errors or
warnings and only `propext`, `Classical.choice` and `Quot.sound` reported.
The implemented theorems are
`Langlands.Analysis.OperatorIdeals.hilbertSchmidtBasisIndependence` and
`Langlands.Global.ArchimedeanGL.finiteUniformDifferentialGrowth`.
These are development checks, not exact-target acceptance receipts. Neither
proof has a submitted proof candidate or accepted-public proof. Focused proof
children must await publication of the unchanged target pairs in the workspace
base; the standing program's `lean.peer@1` policy does not accept proofs.

### H1 corrections and retained analytic inputs

Worker 352 reported and explained an impossible-input defect in the former
Hecke-twist and relative-gamma statements: `CommonTwistEulerInputs` fixed the
partial Euler tails for each character before the common exceptional set `B`
was chosen for two characters. Even the trivial-character GL_1/Q tail cannot
represent all products outside varying enlarged sets `B`. Candidates
`058a793b-eb6a-4ef2-aa3b-0156afeb4ab9` and
`d363da8c-6243-449c-a4ad-0e44b61621a3` were withdrawn.

The correction keeps the local factor system fixed by the character while
indexing partial tails and their analytic data by both the character and `B`.
This repairs the indexing obligation without assuming the global functional
equations, ramified cancellation or factor certificates proved. The following
replacement/new candidates passed machine validation in Worker 116's inspected
fetches, with independent review and publication still pending there:

| Target, with prefix `Langlands.Global` | Candidate | Machine validation |
| --- | --- | --- |
| `FunctionalEquationComparison.HeckeTwistComparisonStatement` | `5998c54a-b4fc-48d1-ad48-b11c8b2ab04a` | `be29a022-dd15-4aff-9409-b414be67bfea` |
| `FunctionalEquationComparison.RelativeGammaComparisonStatement` | `08b15853-e79e-4e92-a5cd-4865ad28df0a` | `daf4afd4-d1f7-4675-93e1-a3f35737dfb5` |
| `FactorSeparation.CertifiedFactorSeparationStatement` | `192e3bbe-5c12-4748-ad80-5cfa620cfd0f` | `4e9bd880-9968-4f8e-afd5-1dc34fc8fd16` |

Worker 352 also reported independent approval, still without publication, for
the generic finite/germ comparison candidates
`3b672bcc-5b63-416b-b26c-cc7cff7359e7` and
`3c6deaf2-58d6-4fab-b274-eb35713bf5c5`, and four compiling private proofs in
H1 draft revision 4. These are attributed reports, not independently recovered
public-proof receipts. In a later message, Worker 64 reports an independent
recheck of the four-proof chain (`3546ec43-613b-4ad0-a904-644f68020e37`),
five compiling private pole/pairing/Appendix/separation proofs, and Worker 352's
report that all four comparison targets now have semantic approval but remain
unpublished. Thus the direct-fetch review status above precedes that later
reported approval for the corrected Hecke and relative-gamma targets. Worker 64
also reports the previous local targets and GammaSeparation proof still staged.
The original L1 and GammaSeparation rows remain historical; this continuation
does not promote them to public results. The two H1 owners will coordinate their
respective exact-target proof children after publication; no duplicate children
or unconditional `AssociatedFactorStatement` proof is claimed.

### H2 statements, proof and focused construction tasks

Worker 116 fetched the first three units below: all had machine validation and
independent semantic approval, with `accepted: false` and `public: false`.
The fourth row is explicitly Worker 84's later report, also consistent with the
parent task's staged-candidate inventory.

| Unit and exact declaration, with prefix `Langlands.Global` | Candidate and review | What remains |
| --- | --- | --- |
| Paired-place realization, `HarrisPairedPlaceRealizationStatement` | `6ad86e30-a541-496c-a71c-f1ff0774e56c`; Reviewer 8784, review `c4f2544a-e64b-4af2-8728-279475dccd19` | CM composita and two compatible place pairs are a statement target. Full intermediate towers, characters and Harris assembly are separate. |
| Conditional assembly, `CMRegularUnitPrescriptionOfInputsStatement` | `587ac5b2-ae19-4adb-8b6f-a71169b5c3b2`; Reviewer 8702, review `a21eb6b3-f969-407e-8457-ef68182f9940` | Three explicit existence inputs imply regular integral-unit prescription. The target does not discharge any of these inputs; its private proof is not a public proof. |
| Integral-unit extension proof, `integralUnitCharacterExtension` of `IntegralUnitCharacterExtensionStatement` | `907cddb9-fa40-4ce7-ad22-f1686e6456c3`; Workers 55/4; Reviewer 8718, review `e4ef24c3-d455-449f-adc3-cbff55788356`; exact-target validation `c3d76201-f8a2-431d-9772-b4f12b48e9f3` | Independent approval and exact-target validation are recorded, but publication is still pending in the fetched state. No public H2 proof is credited by this continuation. |
| Finite-prescription reduction, `CMFiniteCharacterPrescriptionOfFiniteOrderStatement` | Worker 84 reports `6fde0ff6-0dc3-4f95-a947-528bf6e66939`, machine approval and Reviewer 8829 approval, unpublished | Exactly `FiniteOrderCharacterPrescriptionStatement → CMFiniteCharacterPrescriptionStatement`. It isolates a reduction, not a construction of its finite-order premise. |

The following five child contracts were read in full by Worker 116. Their
publication is a division of proof obligations, not proof evidence. No current
executor availability is asserted here.

| Focused task | Target or boundary |
| --- | --- |
| `5d3fa9f5-583e-4227-9d88-f0246a9e7d13` | `SplitAuxiliaryQuadraticsStatement`: actual split auxiliary quadratics. |
| `edbebd3e-c4a7-4171-b395-b24eecf1e910` | `TotallyRealGaloisRealizationStatement`: actual totally-real realization and completion/Galois comparisons. |
| `d44b3215-6631-4a92-af4d-68e79932509e` | `IntegralUnitCharacterExtensionStatement`; the pending proof above belongs to this focused branch. |
| `5c0e9600-5678-46ea-8351-e2e2d89de000` | `FiniteOrderCharacterPrescriptionStatement`: retains the order bound 2n and the whole infinity component. |
| `b98ece58-696e-48f4-83d3-5dbd7d6743f4` | `CMUnramifiedInfinityRealizationStatement`: retains one common positive scaling and unramifiedness at every finite place. |

The auxiliary exact-stabilizer construction, its all-primes depth argument,
unit-norm-to-Weil transport, the solvable tower and the full Harris adapters
remain required as described in the historical H2 table. In particular, these
new tasks and reductions do not remove the residue-characteristic-2 issue or
the half-norm parity and central-character comparisons.

### Algebraic routing and quotient conventions

Worker 116 checked the structural routing supplied by Worker 1107 against the
current Library names for actual corepresented coefficient points, GL_n points,
`Dynamic.semidirectEquiv`, relative roots, lattices and adjoint constructions.
Standard-parabolic child `8ace819d-9522-4381-aaab-f9a84a07755e` and
rational-character/split-component child
`0d8de1ec-d335-4ab1-8a62-53e04510a7f5` isolate algebraic prerequisites.
The algebraic determinant of `Ad` on `Lie U` and general structure proofs remain
with that program; adelic moduli and their comparisons remain with L1.

For the GH quotient convention, `A_G` is the identity component of real points
of the greatest Q-split torus in `Res_{F/Q} Z_G`. It must not silently become
the greatest F-split central torus. At rank zero, the scalar map from `G_m` to
`GL_0` is not a closed immersion: an actual split-central construction must use
the trivial torus there or state a positive-rank restriction. These boundaries
were communicated to the algebraic owners. Workers 94/112 retain the distinct
strict MW95 and weak GH Siegel domains and construct the quotient/measure data
without storing the desired analytic conclusions as input fields.

The continuation was prepared by Worker 116 with Worker 84's H2 updates and
Worker 94's program and analytic-foundations work. Peer reports are attributed
where they have not been replaced by direct receipt inspection. Neither track
of the standing program is complete.


## 2 November 2026 operator-trace publication snapshot

Worker 116 checked this focused continuation against Library
`9d1720cbedcfd184cf48bf36249fc3029583cafa`. The earlier dated tables remain
historical snapshots. The three rows below supersede earlier pending statuses
for these exact units. They do not update the H1/H2 status tables or assert
completion of any L1 analytic theorem.

| Exact public interface | Independently checked publication evidence | Scope |
| --- | --- | --- |
| `Langlands.Analysis.OperatorIdeals.traceNormBasisIndependence` in [TraceNormBasisProof.lean](../../Langlands/Analysis/TraceNormBasisProof.lean), proving `TraceNormBasisIndependenceStatement` | Proof `f01a6f2e-3b22-4c81-a08a-8a02b5d15a6e`; child `4c0f9ccf-238f-4bcb-a01a-b8baff2bd922`; unqualified Reviewer 9471 approval; accepted Lake and exact-target validation `35aa70a1-908c-45bc-a669-de9423422602`; publication `1271a6b7c9a470deaa1b8e2aadc2e2defd10f5b5`, integration `751260a0035d4a94b62ad5060d9629da`. | The existing existential trace-class predicate is equivalent to summability of the positive real left-modulus diagonal in every supplied Hilbert basis, and the resulting `traceNormIn` sums agree when summable. Three independent universe parameters; no separability assumption. This result does not concern the full complex diagonal of A. |
| `Langlands.Analysis.OperatorIdeals.leftModulusFactorization` in [LeftModulusFactorizationProof.lean](../../Langlands/Analysis/LeftModulusFactorizationProof.lean), proving `LeftModulusFactorizationStatement` | Proof `9f9c6bdc-bbf6-4d4e-9b62-00745d361e41`; child `977b344d-0568-4971-b295-66e5694b2b2a`; unqualified Reviewer 9510 approval; accepted Lake and exact-target validation `2a6c3564-4c6e-4ad9-9803-ce9897e471af`; publication `5d3754ec863f6d5013aca65cbcec0801e6972d1f`, integration `9a95ec945b4347de94e99d1f42370faf`. | For every bounded complex-linear endomorphism A of an arbitrary complete complex inner-product space, there is U with norm at most one and `A = (leftModulus A).comp U`. The proof uses continuous extension from a range closure, orthogonal projection and adjoints. It asserts no partial-isometry property. |
| `Langlands.Analysis.OperatorIdeals.HilbertSchmidtProductTraceStatement` in [HilbertSchmidtProductTraceStatement.lean](../../Langlands/Analysis/HilbertSchmidtProductTraceStatement.lean) | Statement `29ceb1e6-cdc1-4ed3-8891-ca6596a5383a`; unqualified Reviewer 9618 approval; machine validation `4a7a2074-9e54-46da-bda4-f7d26f9fb4b8`; publication `9d1720cbedcfd184cf48bf36249fc3029583cafa`, integration `314a17deda364fae838feda27cd74906`. | A public proposition target only. For rectangular Hilbert–Schmidt maps B:E→F and C:F→E, it asserts absolute summability of the complex diagonals of CB and BC and equality of their specified-basis `traceIn` sums. The spaces and basis index types have four independent universes. It does not assert trace-class membership of either product. |

The three artifact records were fetched directly, including their independent
review verdicts, accepted machine checks and publication records. Their target,
proof where applicable, and transitive project-import Lean/Markdown pairs match
the named current Library. The proof authorship of the first two rows is
Worker 116; the focused proof children performed their own submission and
independent review.

The complete product-trace proof pair is available in unreviewed parent draft 8:
`drafts/34b81620-20d7-4059-9b08-6bedd1c1c029/revision-8-eb124052a67ad2dd291a1e8e0aa1ea1dd3ff6ce4a6ce9306ae4a44914f234eb2/files`.
Worker 116 published exact-target proof child
`5e90d0a0-1d55-4ccb-8005-e00c990dbee7` after current task, Library and DAG
searches. Recovery development check
`b20b48a9-d975-42de-afd6-15c94ce27cea` compiled the proof with zero errors
and warnings and only the three standard axioms. The inspected child has no
candidate. Development compilation and task publication supply no accepted
proof evidence.

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
remain distinct obligations. Actual automorphic convolution trace class,
closedness of the cuspidal space, rapid decay, algebraic/Hilbert comparison and
the general-reductive spectral decomposition are still required. The operator
publications alone establish none of those conclusions.


## 3 November 2026 trace proof continuation

Worker 116 verified the following focused operator updates against Library
`ca102a8a50473f5a0f03f7fcd16cd21d996a6f7d`. Earlier dated sections retain their historical statuses.
This continuation updates only the named operator units; the H1/H2 tables and
the general-reductive analytic obligations remain as recorded above.

| Exact interface, with prefix `Langlands.Analysis.OperatorIdeals` | Verified status and evidence | Scope and remaining work |
| --- | --- | --- |
| `hilbertSchmidtProductTrace` in [HilbertSchmidtProductTraceProof.lean](../../Langlands/Analysis/HilbertSchmidtProductTraceProof.lean), proving `HilbertSchmidtProductTraceStatement` | Proof `fcb06bdf-fc5e-420c-96ae-473c1880749f` is independently accepted/public at `405ff58c5df69766419c9941161444531c1979ae`, integration `3b9ad820a6fc4e04871026ea366611c4`; Reviewer 9950 approved without qualifications; Lake/exact-target receipt `782e00fa-cc67-48b1-a898-9785133ad807`. Child `5e90d0a0-1d55-4ccb-8005-e00c990dbee7` completed. | Rectangular Hilbert–Schmidt maps have absolutely summable complex diagonals for both compositions and equal specified-basis sums. The spaces and basis indices have four independent universes. This theorem alone does not assert trace-class membership of the compositions. |
| `traceClassFactorization` in [TraceClassFactorizationProof.lean](../../Langlands/Analysis/TraceClassFactorizationProof.lean), proving `TraceClassFactorizationStatement` | Proof `4db18dfb-bcfa-4c3d-b1a6-c536306f4022` is independently accepted/public at `6e277941a7bd32cdcf50123da3df2754259d6be7`, integration `157b691f248645d1b32a66f5e217511e`; Reviewer 10230 approved without qualifications; Lake/exact-target receipt `767e0fa5-2d8b-4c10-adec-352e0ec244a4`. Child `9a7c9e75-bdb5-4697-a6e2-ab817621c66b` completed. | Every actual trace-class endomorphism A of an arbitrary complete complex inner-product space factors as `A = B.comp C` with both factors Hilbert–Schmidt on that space. The positive square root of the left modulus, its contractive factorization and bounded precomposition give the implemented proof. |
| `TraceBasisIndependenceStatement` in [TraceBasisStatement.lean](../../Langlands/Analysis/TraceBasisStatement.lean) | Statement `ee9f64d1-e36e-4968-a705-49c41c881a4c` is independently accepted/public at `405ff58c5df69766419c9941161444531c1979ae`; Reviewer 9801 approved without qualifications; machine receipt `eb97bddb-ca22-4c42-b831-59132843a4e6`. Exact proof child `63eb83e9-da0f-4d3a-bcbf-51c98a1fa3e2` revision 1 is published for adoption of Worker 116's complete draft pair. | The target asserts absolute complex-diagonal summability and equal `traceIn` sums in any two supplied Hilbert bases, with three independent universes. The complete draft compares both sums to one reversed Hilbert–Schmidt product. A public statement and a published child contract do not constitute a public proof. |
| `HilbertSchmidtProductTraceClassStatement` in [HilbertSchmidtProductTraceClassStatement.lean](../../Langlands/Analysis/HilbertSchmidtProductTraceClassStatement.lean) | Statement `67eeed99-0f83-4bae-9484-368dffba3b79` is independently accepted/public at `405ff58c5df69766419c9941161444531c1979ae`; Reviewer 9854 approved without qualifications; machine receipt `1e92a967-add4-4a58-a4c3-8fa7373a818f`. Proof `67b74eb1-3883-4128-aab2-6b434bb5884a` in [HilbertSchmidtProductTraceClassProof.lean](../../Langlands/Analysis/HilbertSchmidtProductTraceClassProof.lean) is independently accepted/public at `a89596feabc7e1db11dbefead1032c9cfc0d1409`, integration `8ccbe1a20ecd481bab8cba13e4ac2ce2`, with accepted Lake/exact-target receipt `a760f96e-9105-4266-ba4f-6703f16c1d4d` and unqualified Reviewer 10254 approval. Child `94138e49-882a-46de-a4b6-b76400ec61b7` completed. | For arbitrary rectangular Hilbert–Schmidt B:E→F and C:F→E, the actual composition `C.comp B` is trace class. Two independent space universes. The published proof constructs a factorization of the left modulus through the composition, then applies absolute product-diagonal summability. |
| `TraceClassIdealStatement` in [TraceClassIdealStatement.lean](../../Langlands/Analysis/TraceClassIdealStatement.lean) | Statement `38331f97-c1dd-4e79-a981-d1fb764021b6` is independently accepted/public at `6820dc99b5972ed5761be21b4ac8afeba7584644`, integration `f02924af8b5548c78958499bb07a2f6d`; Reviewer 10053 approved without qualifications; machine receipt `b393790e-6f39-49dc-8d64-49df7db3ee54`. Both proof prerequisites are public. Exact-proof child `aed42b32-21e0-43a8-b3cb-9ed9f8edd679` revision 1 is published for adoption of Worker 116's complete draft pair; its own independent acceptance and publication remain required. | Zero, addition, complex scalar multiplication, adjoint equivalence and bounded rectangular sandwich laws for the actual trace-class predicate, in two independent universes. Addition factors through the actual Hilbert direct sum `WithLp 2 (E × E)`. This statement supplies no proved trace-norm bound or trace linearity. |

The three public proof pairs and three public statement pairs above byte-match
the named Library. Before publishing the trace-basis child, Worker 116 also
checked all twelve transitive project import pairs against public Library
`a89596feabc7e1db11dbefead1032c9cfc0d1409` and searched current tasks, the whole
Library and both planning DAGs for overlapping work. The child adopts only
`TraceBasisProof.lean` and its paired Markdown from shared program draft 12,
preserving Worker 116 as actual coauthor. The product trace-class child
similarly adopts only its own pair. Draft adoption preserves authorship and
does not supply independent acceptance. Before publishing the ideal-law child,
Worker 116 verified all fourteen transitive project import pairs against
`ca102a8a50473f5a0f03f7fcd16cd21d996a6f7d` and repeated current TaskHub, native
task, whole-Library and both-DAG duplicate searches. The ideal child adopts
only `TraceClassIdealProof.lean` and its paired Markdown from shared draft 12,
with Worker 116 retained as actual coauthor.

Recovery compilation `9a481fb2-4b10-4cb7-ba3c-94213f9713a0` checked five trace
proof modules, including the public product-diagonal module, with zero
errors and warnings. Trace-basis declaration inspection
`3fa61b3b-bbe3-45e8-9ab2-563914df4c2c` confirmed the three independent universe
parameters and only standard axioms. Ideal-law declaration inspection
`8e687fac-14c4-47e2-9055-c6772c4b717e` likewise confirmed u/v and standard
axioms with zero errors/warnings. These are development checks. The proof
children retain their separate Lake, exact-target, semantic-review and
publication obligations.

Source conventions remain Getz–Hahn, Definition 9.1.1 and the trace discussion,
printed pp.240–241, and Exercises 9.1–9.2, p.267, with the complete October 2026
errata checked. The source assumes separability. Arbitrary basis indices,
rectangular spaces, the Hilbert–Schmidt factorization of trace-class maps and
the ideal-law collection are documented internal extensions. The positive
left modulus is sqrt(A A*); the complex diagonal uses Mathlib's inner product
linear in its second variable. The public proof Markdown explains the
implemented arguments and does not attribute these exact broader quantifiers
to the original source.

Canonical trace construction and linearity, trace-class ideal proofs and
publication of the remaining operator proofs still require their own units.
Actual automorphic convolution trace class, cuspidal closedness, rapid decay,
algebraic/Hilbert comparison and the general-reductive spectral decomposition
remain required L1 obligations. No operator result in this continuation
establishes those conclusions or changes the conditional H3/H4 boundaries.


## 3 November 2026 first-order auxiliary-character continuation

Worker 84 checked this focused H2 continuation against Library
`622054b9c6b9f07feb1335165348ac66b27b39e5`. It supersedes the older pending
statuses only for the exact units named here. Other H1/H2 rows and all general
reductive analytic obligations remain historical snapshots. This continuation
credits public proposition targets and the existing conditional reduction.
At that snapshot, none of the new auxiliary-construction proofs below was
independently public. The 4 November update records the later trace-stabilizer
proof publication and distinguishes the other reviewed candidates from public
proofs.

The five targets in the next table were fetched as accepted/public, with
terminal accepted machine validation and unqualified independent semantic
approval. Their current Lean/Markdown pairs match the frozen pairs. The first
three were published in `25b91125ea94e88d741b206d633e82eb0d87c3e5`; the last
two in `071b82c1a715daffe0334ad25311484eaba312b0`. All remain in the named
current Library. Each is a focused internal prerequisite of the first-order
route, rather than a theorem attributed verbatim to Harris or Henniart.

| Exact public target | Acceptance evidence | Exact proof child and scope |
| --- | --- | --- |
| `Langlands.HarmonicAnalysis.PadicFiniteCoefficientSeparationStatement.{u}` in [PadicFiniteCoefficientSeparationStatement.lean](../../Langlands/HarmonicAnalysis/PadicFiniteCoefficientSeparationStatement.lean) | Statement `a2a18383-76cc-4d4c-a399-a8948e486dca`; Reviewer 11284; publication integration `50a76e5a1dd549aabbfb4522644e7c67`. | Child `96fb825e-83e9-473c-a3cf-2c2ddee9b04e`, revision 1, has Worker 84's complete adoption pair. One inverse-prime-power threshold detects every nonzero coefficient in a finite set on the actual additive integer lattice. Proof acceptance/publication is pending. |
| `Langlands.LocalClassField.QuadraticNormTraceStatement.{u,v}` in [QuadraticNormTraceStatement.lean](../../Langlands/ClassFieldTheory/Local/QuadraticNormTraceStatement.lean) | Statement `c36f24a4-b0d8-42b8-8cd9-4b5892b76fce`; Reviewer 11346; integration `1f0c10f85e6b4ecba20ffdda93ce10f1`. | Child `6913393c-dd2a-4185-8b5c-bdb7f28db90c`, revision 1, has Workers 84/27's complete adoption pair. For every integral a and y in a finite compatible extension, the actual norm is `1+a*Tr(y)+a^2*r` with integral r. Every prime, independent universe and finite degree is retained. Proof publication is pending. |
| `Langlands.HarmonicAnalysis.PadicDeepUnitCharacterStatement.{u}` in [PadicDeepUnitCharacterStatement.lean](../../Langlands/HarmonicAnalysis/PadicDeepUnitCharacterStatement.lean) | Statement `27d5bbbf-8ea7-4816-ad3e-a258a7ba8065`; Reviewer 11380; integration `bea03ede39414874a66a155c048cf5dc`. | Child `6e7cdd5e-2510-439f-a502-58183ad32535`, revision 1, has Worker 84's complete adoption pair. The explicit conductor bound kills the multiplication error in the prescribed character `u ↦ psi(c*(u-1))` on actual principal units, with a uniform p-power annihilator. Character extension, nontriviality and stabilizers are separate. |
| `Langlands.HarmonicAnalysis.PadicPrincipalUnitCharacterExtensionStatement.{u}` in [PadicPrincipalUnitCharacterExtensionStatement.lean](../../Langlands/HarmonicAnalysis/PadicPrincipalUnitCharacterExtensionStatement.lean) | Statement `d6ed3b3f-ab9f-4d22-be4f-0ebde529978f`; Reviewer 11433; integration `0ed04b44ca4e44b3af18890c3a7bd851`. | Child `acba9920-7450-4aff-b276-4ef3ca6ec471`, revision 1, has a complete adoption pair preserving Workers 84/394/55/450. Every continuous complex character of actual principalUnits n extends to finite positive order on field units, with value one at the supplied uniformizer. All supplied compatible topologies, p=2 and n=0 are retained. |
| `Langlands.HarmonicAnalysis.PadicDeepUnitNormTraceStatement.{u,v}` in [PadicDeepUnitNormTraceStatement.lean](../../Langlands/HarmonicAnalysis/PadicDeepUnitNormTraceStatement.lean) | Statement `d6f2b22f-8e27-44e8-b5bb-4027f526d2b1`; Reviewer 11452; integration `5d3c0966bb27414bb2b05ed7d28c8bb1`. | Child `f2ecd102-7b20-492c-b1b4-3d2c3c4c4404`, revision 1, has Workers 84/27's complete adoption pair and formally requires the quadratic proof child under `lean.proof@1`. Under the prescribed character formula and three valuation bounds it constructs the actual unit z=1+i(a)y, puts its norm in principalUnits n and computes `chi(Nz)=Circle.toUnits(psi(c*a*Tr(y)))`. |

The public algebraic `Langlands.Global.PrimitiveTraceStabilizerStatement` has
separate exact proof child `0cd7bcab-0ab1-4373-8276-18db068b787f`, revision 1.
At the 3 November snapshot it had Worker 84's complete adoption pair and
remained a prerequisite proof obligation; its later publication is verified
below. Public theorem imports alone confer no authorship on a downstream
implementation.

### Complete private assembly and independent proof boundaries

The unchanged public targets are
[AuxiliaryCharacterStatement.lean](../../Langlands/Global/Arithmetic/AuxiliaryCharacterStatement.lean)
and [GeneralPositionStatement.lean](../../Langlands/Global/Arithmetic/GeneralPositionStatement.lean).
Their original-source correspondence remains Henniart 2000 §3.4 condition 3,
p.449, and §3.6 Lemma 3, p.451; Harris 1998 Definition 4.5 and Lemma 4.7,
p.201, with (4.12)–(4.13), pp.204–205. This continuation reuses their reviewed
source correspondence and leaves both target pairs unchanged. The first-order
implementation below is an internal alternative route. It is not attributed
to the literal source argument using an embedding of `(Z/2^N Z)^x`.

Worker 84's complete private implementation
`Langlands.Global.auxiliaryCharacterFirstOrder.{u,v}` compiles at the declared
`AuxiliaryCharacterStatement.{u,v}` type with zero errors/warnings and only
propext, Classical.choice and Quot.sound (development diagnostic
`764abe12-da42-4b69-a7ee-f7b151dc44a8`). The checked development includes
complete private copies of its six prerequisite proofs. It constructs finite
order, strict arbitrary-depth nontriviality and the actual exact norm stabilizer
for every prime, including two, every compatible finite Galois overfield and
every intermediate field. This is development evidence, with independent
exact-target validation and semantic acceptance still required.

Exact proof child `de89b95c-fc2c-453c-96ec-5b1b74522c43`, revision 1,
contains a complete seven-pair adoption bundle: the main proof plus integral
detection/trace helpers, topology comparison, the first-order family,
norm coordinates, the conditional exact stabilizer and depth helpers. Its
formal `lean.proof@1` requirements name all six prerequisite proof children
above. The adoption bundle contains none of their private proof copies. Those
results must be independently accepted/public and imported by their current
Lean names before the final proof is submitted. The audit found 48 other
project imports already public and paired, seven new own modules and exactly
those six pending proof modules.

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

The already public `Langlands.Global.auxiliaryGeneralPositionReduction` proves
`AuxiliaryCharacterStatement.{u,u} → HarrisGeneralPositionStatement.{u}`.
Its exact proof `328d43dd-29ec-4ae1-9635-170a2a9933e2` and completed child
`4ae81b3a-b844-496c-9fe9-9de905f477c0` preserve Workers 20/84 authorship.
It remains a conditional reduction, rather than an auxiliary existence proof.
Worker 84's private composition `Langlands.Global.harrisGeneralPosition.{u}`
now compiles cleanly by applying that reduction to the complete first-order
construction (diagnostic `4a76aca2-1b78-4f4f-813d-c769260098b1`, universe u,
standard axioms). Separate child `83445b71-56bc-4dab-b2df-43a956708a18`,
revision 1, has the complete composition pair and formally requires the
auxiliary proof child. Its public reduction-import closure contains 100 project
modules; those pairs are byte-identical in the checked current Library.

This composition retains the explicit normalized-reciprocity hypothesis of the
last two Harris conjuncts. It constructs no reciprocity family and supplies no
proof of NormalizedSystemExistence. The current-task, whole-current-Library and
both-DAG searches preceded each new child; the existing statement task
`91266440-3276-48dc-ab77-8d1c1fa386e8` and all neighboring proof owners retain
their scopes. Complete adoption content and task publication are coordination
evidence. The local construction does not yet supply an independently public
auxiliary or Harris proof, prescribed global Hecke characters, paired field
towers, weak automorphic induction or H2 completion.

## 4 November 2026 trace-stabilizer proof publication

Worker 84 verified this update against Library
`9caf47cacd8f25d9a56aa0737b4256267bf62d16`. The exact proof
`cdaf4899-ba07-4084-9784-51a6d625c5e8`, bound to child
`0cd7bcab-0ab1-4373-8276-18db068b787f` revision 1, is accepted/public.
Its theorem is `Langlands.Global.primitiveTraceStabilizer.{u,v}` in
[PrimitiveTraceStabilizerProof.lean](../../Langlands/Global/Arithmetic/PrimitiveTraceStabilizerProof.lean),
with its [paired proof explanation](../../Langlands/Global/Arithmetic/PrimitiveTraceStabilizerProof.md).
The candidate retains Workers 1604/84 as actual coauthors. Machine receipt
`8b4fa3b2-5bcc-4e4b-92ca-cf4c26b78b61` passes Lake build, exact target,
unchanged statement and frozen inputs. Reviewer 13649 independently approved
the exact candidate without qualifications; review
`deaab63f-5c77-400c-b246-7cb18fe3626c` and integration
`e884f6c2c1274b768b1ec4b80fff6b85` record its publication in
`476a152fd90d846bcb20b9897f53829a768b822c`. The current proof pair matches
the frozen pair, and the target pair remains unchanged.

For any finite separable extension M/F and actual intermediate field L, the
theorem produces a nonzero primitive coefficient a in L such that preserving
`x ↦ Tr_M/F(a*x)` by precomposition is equivalent to pointwise fixation of L.
It retains independent field universes, arbitrary characteristic and no
normality hypothesis. The implemented proof combines trace invariance and
nondegeneracy with primitive-element generation and the actual inclusion of L.
It proves the algebraic prerequisite; multiplicative character existence,
continuity, finite order, norm compatibility and arbitrary depth remain
separate conclusions of the auxiliary construction.

At this 4 November snapshot, four other exact revision-1 proof candidates had
accepted machine validation and unqualified independent semantic approval, but
each fresh fetch reported `accepted=false` and `public=false`. They receive no
public-proof credit in this snapshot; the 5 November continuation below records
the later finite-separation publication:

| Prerequisite | Candidate | Machine receipt | Independent reviewer |
| --- | --- | --- | --- |
| Finite coefficient separation | `a0a31834-071d-45e0-bee5-789d6adb821d` | `69776751-b4e5-47f3-8dba-961cf5509c53` | Reviewer 13782 |
| Integral quadratic norm–trace error | `bdda102e-f94e-440b-9d80-a73119ce037f` | `e82f52de-a933-47e1-b58d-f1a39c2c8529` | Reviewer 13785 |
| Prescribed deep-unit character | `8d823b60-4753-4152-8203-20c3b9bed6a9` | `e7e4a8f6-37dd-47db-934a-38834b31e645` | Reviewer 13781 |
| Normalized principal-unit extension | `ddea3250-b089-483f-944f-ad658256f4a1` | `85c587ba-37be-4258-8c58-4a3f95b22ad7` | Reviewer 13794 |

The auxiliary child's six formal prerequisite requirements are preserved:
the trace-stabilizer proof now has verified publication, while the other five
proof publications remain required, including the norm–trace character
comparison. The auxiliary and Harris assemblies themselves also retain their
separate independent proof and publication gates. Fresh private recompilations
`7080a225-e164-4e6d-8a63-547b11f69d25` and
`ae3d1cb1-7c5d-4d31-ba28-5ecfa69445be` have zero errors and warnings, full
declared universes and only propext, Classical.choice and Quot.sound. They remain
development diagnostics. The explicit normalized-reciprocity premise, global
field/tower and Hecke-character obligations, and all H2 and general automorphic
completion conditions remain in force.

## 5 November 2026 finite-separation proof publication

Worker 84 verified this focused continuation against Library
`a9f12d1e4a0823c676b8a7b9292f17ea7c1d08ee`. Exact proof
`a0a31834-071d-45e0-bee5-789d6adb821d` is now accepted/public under
`lean.proof@1`. Its theorem
`Langlands.HarmonicAnalysis.padicFiniteCoefficientSeparation.{u}` in
[PadicFiniteCoefficientSeparationProof.lean](../../Langlands/HarmonicAnalysis/PadicFiniteCoefficientSeparationProof.lean)
proves the unchanged public proposition
`Langlands.HarmonicAnalysis.PadicFiniteCoefficientSeparationStatement.{u}`;
the [paired explanation](../../Langlands/HarmonicAnalysis/PadicFiniteCoefficientSeparationProof.md)
describes the implemented proof. The candidate preserves Workers 1649/84
authorship. Machine receipt `69776751-b4e5-47f3-8dba-961cf5509c53`
passes Lake build, exact target, unchanged statement and frozen inputs.
Reviewer 13782 approved without qualifications in review task
`92e14868-e9cf-415e-82a9-54b56c1f1606`. Integration
`fd63b01119c4496e83893196c237c6c0` published the proof in
`409542525904dd50036abafdafb8ad1459eadade`. Fresh task inspection confirms
child `96fb825e-83e9-473c-a3cf-2c2ddee9b04e`, revision 1, is done, with
closed completion `779090a1-d01a-415a-aa6c-d071961be543`. Current Library
and workspace proof/target pairs match their original hashes.

The proof chooses a finite maximum of coefficient-order bounds. For every
later exponent, the published lattice-annihilator implication and positive
integer order of the actual prime exclude triviality for each nonzero
coefficient; a zero coefficient gives triviality directly. The exact target
retains every prime including two, arbitrary carrier universe, supplied
compatible topology, every integer lattice level and empty coefficient sets.
This is an internal additive separation result. It constructs no multiplicative
auxiliary character or norm stabilizer.

Together with the trace-stabilizer proof above, two of the auxiliary child's
six prerequisite proofs now have verified publication and completed exact
children. All six formal dependencies remain. At this snapshot the quadratic
norm–trace, prescribed deep-unit character, principal-unit extension and
norm–trace character-comparison proof publications remained separate gates;
the first three have the reviewed candidates recorded above, and the
continuation below records their later publication. The auxiliary and Harris
assemblies also retain their own independent proof and publication gates.
Fresh development check `f422467c-d5b4-411c-b199-2f2e9adaa765` compiles
both private assembly modules with zero errors or warnings and supplies no
public-proof credit. The explicit normalized-reciprocity premise and the
global field/tower, Hecke-character, H2 and general automorphic obligations
remain unchanged.

## 5 November 2026 quadratic, deep-unit and principal-unit proof publications

Worker 84 verified this focused continuation against Library
`ee0c0dd6da0a631f199c2bc0aa6040eece98f41d`. Three more exact revision-1
prerequisite proofs of the auxiliary child are accepted/public under
`lean.proof@1`. All three were published in
`0d12b7d171600d15516e52ee508d3aaca3e9cf9e`. For each one, the machine receipt
passes Lake build, exact target, unchanged statement and frozen inputs. Each
independent reviewer approved without qualifications. Fresh task inspection
shows each exact child done, with a closed completion. The proof and target
pairs in the frozen candidate, the publication commit, the current Library and
the workspace have identical hashes.

| Prerequisite and theorem | Candidate and authors | Machine, review and integration | Exact child and completion |
| --- | --- | --- | --- |
| Integral quadratic norm–trace error, `Langlands.LocalClassField.quadraticNormTrace.{u,v}` in [QuadraticNormTraceProof.lean](../../Langlands/ClassFieldTheory/Local/QuadraticNormTraceProof.lean) ([explanation](../../Langlands/ClassFieldTheory/Local/QuadraticNormTraceProof.md)) | `bdda102e-f94e-440b-9d80-a73119ce037f`; Worker 1651 with Workers 84/27 | `e82f52de-a933-47e1-b58d-f1a39c2c8529`; Reviewer 13785, review `bae93660-a5b1-4429-9064-e6991ff01e78`; integration `dd3ce3f95b144c5e96a5b4e00a15c463` | `6913393c-dd2a-4185-8b5c-bdb7f28db90c`; `5375bd39-0262-4705-a7d2-52ddc15f8f98` |
| Prescribed deep-unit character, `Langlands.HarmonicAnalysis.padicDeepUnitCharacter.{u}` in [PadicDeepUnitCharacterProof.lean](../../Langlands/HarmonicAnalysis/PadicDeepUnitCharacterProof.lean) ([explanation](../../Langlands/HarmonicAnalysis/PadicDeepUnitCharacterProof.md)) | `8d823b60-4753-4152-8203-20c3b9bed6a9`; Worker 1652 with Worker 84 | `e7e4a8f6-37dd-47db-934a-38834b31e645`; Reviewer 13781, review `b198e606-5bed-4cf2-83fd-a21abc1bfe4b`; integration `91ce7258400546f5a4d29988bb361e5a` | `6e7cdd5e-2510-439f-a502-58183ad32535`; `708ea617-5692-4511-a309-7830ec6aaaf1` |
| Normalized principal-unit extension, `Langlands.HarmonicAnalysis.padicPrincipalUnitCharacterExtension.{u}` in [PadicPrincipalUnitCharacterExtensionProof.lean](../../Langlands/HarmonicAnalysis/PadicPrincipalUnitCharacterExtensionProof.lean) ([explanation](../../Langlands/HarmonicAnalysis/PadicPrincipalUnitCharacterExtensionProof.md)) | `ddea3250-b089-483f-944f-ad658256f4a1`; Worker 1657 with Workers 394/55/450/84 | `85c587ba-37be-4258-8c58-4a3f95b22ad7`; Reviewer 13794, review `8ec16aac-714f-4526-b59d-e53c03e39789`; integration `76b3057ff502420cbfde17e5fd186cc0` | `acba9920-7450-4aff-b276-4ef3ca6ec471`; `d807de4e-1be0-49f3-8847-ef3bf334fdd9` |

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

Five of the auxiliary child's six prerequisite proofs now have verified
publication and done exact children: trace stabilizer, finite coefficient
separation, quadratic norm–trace error, deep-unit character and principal-unit
extension. The remaining prerequisite is the norm–trace character comparison,
child `f2ecd102-7b20-492c-b1b4-3d2c3c4c4404` revision 1, whose formal quadratic
requirement is now satisfied. On 5 November it was claimed by Worker 928, with
a running attempt and no candidate artifact. Auxiliary child
`de89b95c-fc2c-453c-96ec-5b1b74522c43` and Harris child
`83445b71-56bc-4dab-b2df-43a956708a18`, both revision 1, were ready and
unclaimed. Each retains its formal requirements and its own independent proof
and publication gates. The finite-separation continuation above
(`7570a91e-072c-4bd2-8b49-2018cee052ec`) is accepted/public after
independent review by Reviewer 13937. The explicit normalized-reciprocity
premise and the global field/tower, Hecke-character, H2 and general automorphic
obligations remain unchanged.

## 5 November 2026 norm–trace character and auxiliary-character proof publications

Worker 84 verified this focused continuation against Library
`570fefbe5133b1afff1a5914f8de20920d97fda0`. The last prerequisite proof of
the auxiliary child and the auxiliary assembly itself are now
accepted/public under `lean.proof@1`. The norm–trace character comparison was
published in `0bd5bf67c3464359bc8da3b3100163d6ee3da352` and the auxiliary
assembly in `910675f18ad6c3d8b09c12c678a0243795a673b9`. For each one, the
machine receipt passes Lake build, exact target, unchanged statement and frozen
inputs. Each independent reviewer approved without qualifications. Fresh task
inspection shows each exact child done, with a closed completion declaration.
Every proof file of each frozen candidate has the same hash in the publication
commit, the current Library and the workspace. The two target pairs are the
same at the candidate base commits, in the current Library and in the workspace.

| Theorem | Candidate and authors | Machine, review and integration | Exact child and completion |
| --- | --- | --- | --- |
| Norm–trace character comparison, `Langlands.HarmonicAnalysis.padicDeepUnitNormTrace.{u,v}` in [PadicDeepUnitNormTraceProof.lean](../../Langlands/HarmonicAnalysis/PadicDeepUnitNormTraceProof.lean) ([explanation](../../Langlands/HarmonicAnalysis/PadicDeepUnitNormTraceProof.md)) | `6f5fd3ed-a3f5-4efc-bddf-6cce37430bf2`; Worker 928 with Workers 27/84 | `2089c33a-4276-498f-8451-58f40bee0286`; Reviewer 14054, review `d49b9971-844c-4327-9f02-2158bb1b35a6`; integration `3d9efda2ffcb46a78e0245f1b45a2b6c` | `f2ecd102-7b20-492c-b1b4-3d2c3c4c4404`; `df0bc878-e21c-499e-a357-929e1f931e49` |
| Auxiliary characters with the exact unit-norm stabilizer, `Langlands.Global.auxiliaryCharacterFirstOrder.{u,v}` in [AuxiliaryCharacterFirstOrderProof.lean](../../Langlands/Global/Arithmetic/AuxiliaryCharacterFirstOrderProof.lean) ([explanation](../../Langlands/Global/Arithmetic/AuxiliaryCharacterFirstOrderProof.md)) | `ed482f0d-91a6-4eb2-ab0d-a11eaa5b890b`; Worker 1652 with Worker 84 | `af083fc1-7c7a-4f6b-9cdd-814cf66a9e47`; Reviewer 14253, review `1e4c0b75-d207-42ab-a23a-388ecb36907d`; integration `66d0e6ca6b2f4738add5c040b071cca1` | `de89b95c-fc2c-453c-96ec-5b1b74522c43`; `2bde004f-418f-409e-90da-776067123308` |

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
odd-prime restriction and no reciprocity premise. The published proof Markdown
documents how this route differs from Harris's logarithmic argument.

All six prerequisite proofs of the auxiliary child and the auxiliary assembly
now have verified publication and done exact children. Harris child
`83445b71-56bc-4dab-b2df-43a956708a18` revision 1, whose formal requirement is
the auxiliary proof task, is in verification. On 5 November Worker 1677 staged candidate
`c86c27e3-68c2-48e8-a621-c80518ed04af` (review task
`9b9f5b82-005b-495f-9159-5c1706df7e34`) with Worker 84 as coauthor. Its Lean
file is byte-identical to the adoption pair named in the child context. Its
Markdown adds an authorship line and states that both imported proofs are
public. At this snapshot the candidate had no machine receipt or review,
and it keeps its own independent proof and publication gates. The composition
keeps the explicit normalized-reciprocity premise and constructs no
reciprocity family. The global field/tower, Hecke-character, H2 and general
automorphic obligations remain unchanged.

## 5 November 2026 Harris general-position and H2 composition proof publications

Worker 84 verified this focused continuation against Library
`ffddfca241fd480a4fb3b8c9215b48c488d7f97b` and rechecked the file hashes
against Library `73016647c403b942bebe18fad4e569a83c342b52` and the current
Library `9d2c31eb3021c9de866cc7f8313284404b3f5ccc`. The
Harris composition and six H2 aggregate compositions are accepted/public under
`lean.proof@1`. Harris was published in
`bc859155612cc8ca34e8e25175ce2f7775c217dc`; ramified twist isolation,
character prescription and CM-character globalization in
`50126e1b2b20b62d408b52dc3552f01089dd1d11`; and the CM finite-order
prescription, regular CM unit prescription and field realization in
`819ea8d4de6f7dde4b0d7f879f58af405e135acf`. For each one, the machine receipt
passes Lake build, exact target, unchanged statement and frozen inputs. Each
independent reviewer approved without qualifications. Fresh task inspection
shows each exact child done, with a closed completion declaration and no
required feedback. Any reader can confirm the done state with a task
inspection. The completion declaration identifiers in the last column come from
Worker 84's inspections with completion records, which TaskHub shows only to a
child's publishers and executors. All fourteen proof files have the same hash
in the frozen candidate, all three Library commits and the workspace. The four
target statement pairs (`CharacterPrescriptionStatement`,
`CMCharacterStatement`, `FieldRealizationStatement` and
`GeneralPositionStatement`) are the same in all three Library commits and the
workspace. Every composition applies published
component theorems only; none adds a definition, hypothesis or axiom.

| Theorem | Candidate and authors | Machine, review and integration | Exact child and completion |
| --- | --- | --- | --- |
| Full local Harris general position, `Langlands.Global.harrisGeneralPosition.{u}` in [HarrisGeneralPositionProof.lean](../../Langlands/Global/Arithmetic/HarrisGeneralPositionProof.lean) ([explanation](../../Langlands/Global/Arithmetic/HarrisGeneralPositionProof.md)) | `c86c27e3-68c2-48e8-a621-c80518ed04af`; Worker 1677 with Worker 84 | `1d78a22f-4688-43f3-b0b8-6a83227c0c93`; Reviewer 14622, review `9b9f5b82-005b-495f-9159-5c1706df7e34`; integration `abe1f20513564fb58082148c19102b92` | `83445b71-56bc-4dab-b2df-43a956708a18`; `6ba8014e-1874-4f51-a3d1-2398d8454652` |
| Ramified twist isolation, `Langlands.Global.ramifiedTwistIsolation.{u}` in [RamifiedTwistIsolationProof.lean](../../Langlands/Global/Arithmetic/RamifiedTwistIsolationProof.lean) ([explanation](../../Langlands/Global/Arithmetic/RamifiedTwistIsolationProof.md)) | `7b46bd25-13c6-49cd-96a0-4efa633bcca9`; Worker 1652 with Worker 84 | `859ee68a-f9be-49ea-8533-268b07115023`; Reviewer 15092, review `c4f2f3d2-a939-4686-836d-67a78ac3dbd9`; integration `17f9fc3e50c146a7a727e30ae7402fee` | `bfd40677-931c-48c9-a0fa-268d1964449c`; `dc9e4e2d-6b3f-41b8-95e8-3bc17c3f4f87` |
| Coherent finite-character prescription, `Langlands.Global.characterPrescription.{u}` in [CharacterPrescriptionAggregateProof.lean](../../Langlands/Global/Arithmetic/CharacterPrescriptionAggregateProof.lean) ([explanation](../../Langlands/Global/Arithmetic/CharacterPrescriptionAggregateProof.md)) | `167eaab1-baee-4d66-a9b5-1d549c7840a0`; Worker 1657 with Worker 84 | `8bafaf59-9a10-4879-aa80-83cb2125fcd2`; Reviewer 15098, review `44034348-7b94-4642-a4de-1424ee15e691`; integration `3ec43ee5601849d6947fc6a184815350` | `a589d250-7cd1-4f6b-9f2e-7236cd2bd64e`; `d6fffc88-f11e-40f1-b89c-701ea81fb1d3` |
| Conjugate-self-dual finite-order CM prescription, `Langlands.Global.cmFiniteCharacterPrescription.{u}` in [CMFiniteCharacterPrescriptionProof.lean](../../Langlands/Global/Arithmetic/CMFiniteCharacterPrescriptionProof.lean) ([explanation](../../Langlands/Global/Arithmetic/CMFiniteCharacterPrescriptionProof.md)) | `6c927f2c-3c8f-4fcd-9e0f-e0b2f1d88558`; Worker 1690 with Worker 84 | `324493ce-2d0f-419e-9d02-4e5b44c18627`; Reviewer 15121, review `0cee3187-1f2e-4885-a608-02da93eb0844`; integration `f942ea7770bb427baca39d38a9a855f8` | `1d50aaf3-559e-4476-8c30-f7c6bf2abf64`; `714743a7-03df-4dbd-a896-ff33d6bf43a7` |
| Regular CM infinity type with prescribed unit components, `Langlands.Global.cmRegularUnitPrescription.{u,v}` in [CMRegularUnitPrescriptionProof.lean](../../Langlands/Global/Arithmetic/CMRegularUnitPrescriptionProof.lean) ([explanation](../../Langlands/Global/Arithmetic/CMRegularUnitPrescriptionProof.md)) | `a55e3533-e93c-4571-8b3c-46a6f17d7a65`; Worker 1691 with Worker 84 | `9a09c64d-de8a-4902-baf8-4ee98c5a6c67`; Reviewer 15128, review `c4104b3b-f705-4975-8a55-6e5b5298fb08`; integration `e7c618cc5551466e9fb53f9e1865831d` | `05a6071e-e68e-407c-b639-4e9a267cf16e`; `29709abf-cabb-4dc1-a5fc-f97e58cf4972` |
| Coherent CM-character globalization, `Langlands.Global.cmCharacterGlobalization.{u,v}` in [CMCharacterGlobalizationProof.lean](../../Langlands/Global/Arithmetic/CMCharacterGlobalizationProof.lean) ([explanation](../../Langlands/Global/Arithmetic/CMCharacterGlobalizationProof.md)) | `6f5c348f-05f8-4902-96a5-84d830e6f179`; Worker 1692 with Worker 84 | `79b29258-c02f-4717-a7cb-6cd61620fb3b`; Reviewer 15117, review `50cca368-d581-4756-bc6a-e73dc4850948`; integration `7e80f2694a944909aadc8b8be620ea26` | `b0a1a07e-7d06-4eea-928a-db2551b76c17`; `104c0c93-8d6e-4a5d-9f4e-237b8dcd7339` |
| Field realization and split auxiliary quadratics, `Langlands.Global.fieldRealization.{u,v}` in [FieldRealizationAggregateProof.lean](../../Langlands/Global/Arithmetic/FieldRealizationAggregateProof.lean) ([explanation](../../Langlands/Global/Arithmetic/FieldRealizationAggregateProof.md)) | `42edd99b-db77-4f01-926d-0a8f0928cca6`; Worker 1693 with Worker 84 | `9e9ba91f-5a8f-4ea1-9a0c-e0f27ff7c051`; Reviewer 15118, review `dc076a2b-102e-4ec9-bf9e-449b69f7dd57`; integration `758fffea71604440a9e4e6eccfda59b1` | `f2efde1c-a30a-4d4b-823f-5b71a3eebaee`; `4f8b6b62-6b96-4d25-9d76-efb02a004f32` |

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

With these publications every H2 aggregate composition of the field
realization, character prescription, CM-character and Harris rows is
accepted/public. The Brauer route for Henniart (2000) §3.7 (p.451) is the
remaining finite-group input. It has five exact revision-1 children with two
different target pairs. The prerequisite finite character theory child targets
`Langlands.FiniteCharacterTheoryStatement.{uG,uV,uW}` in
`Langlands/Representation/Finite/CharacterStatement` (Lean `d6772826`,
Markdown `7a6a6b87`). The four Brauer-specific children target conjuncts of
`Langlands.FiniteRep.FiniteBrauerTheoryStatement.{uG}`, or that aggregate
itself, in `Langlands/Representation/Finite/BrauerStatement` (Lean
`b5f0c11f`, Markdown `196495fe`). Both target pairs are unchanged in all three
Library commits. Their status at Worker 84's task inspections of 5 November
2026:

- Finite character theory, child `0a860318-3018-47ed-b02c-3aec86f49f09`
  (target `Langlands.FiniteCharacterTheoryStatement`, the CharacterStatement
  pair): candidate `e554ecc4-ccce-4a13-825d-88febc4e4432` by Worker 1273 with
  Worker 84, approved by Reviewer 15254 and published in
  `73016647c403b942bebe18fad4e569a83c342b52`. The child is done; completion
  declaration `842a04ab-b5b1-460c-b592-f6e3ecb382e8` (Worker 1273) is closed
  with no required feedback.
- Induced character formula, child `d2cae2f9-cfdf-443c-95cc-cffe37b69fb1`
  (target `Langlands.FiniteRep.FiniteInducedCharacterFormulaStatement`, the
  BrauerStatement pair, with the rank-one order and induced degree as named
  theorems): candidate `49d62ef7-aa26-40b2-aa34-aae7c50e9305` by Worker 1187
  with Worker 84, approved by Reviewer 15293 and published in the same commit.
  The child is done; completion declaration
  `553b7321-ffd2-445c-b3b1-ccd616a449ce` (Worker 1187) is closed with no
  required feedback.
- Irreducible basis, child `6ca4f435-be10-4896-8cb7-2f4dba41cba4` (target
  `Langlands.FiniteRep.FiniteIrreducibleBasisStatement`, with virtual-character
  faithfulness as a named theorem; formal requirement `e554ecc4`, now
  satisfied): claimed by Worker 1429. Candidate
  `d9358f43-ab6c-4460-addb-30f3a25198e4` by Worker 1429 with Worker 84 is
  staged on base `73016647`; its Lean and Markdown files are byte-identical to
  the adoption pair named in the task (`01376985`, `5d94674b`). It has no
  machine receipt or review yet.
- Character lattice, child `0bc7a0fe-3ce6-4d62-9c06-51366702058f` (target
  `Langlands.FiniteRep.IntegralBrauerCharacterLatticeStatement`; formal
  requirement `49d62ef7`, now satisfied; its contribution must include the
  seven-module Anthropic FLT Brauer-induction port with licence and change
  records): claimed by Worker 1696, no candidate.
- Aggregate, child `fc2e1a73-8768-4bfc-a6c4-7f7623548227` (target
  `Langlands.FiniteRep.FiniteBrauerTheoryStatement`, whose new conjunct is
  integral Brauer spanning; formal requirements `49d62ef7` and the completion
  of `6ca4f435` and `0bc7a0fe`): no member; the two task requirements are
  open.

Each child keeps its own independent proof and publication gates. The explicit
normalized-reciprocity premise, the Galois-side global functional equation, the
CM and tower adapters of the Harris input, and the global field/tower,
Hecke-character, H3 and general automorphic obligations remain unchanged.
