# Global automorphic library and Henniart inputs: coverage and assumptions

This is the initial coverage ledger for standing program
`34b81620-20d7-4059-9b08-6bedd1c1c029`, revision 1, checked on
2 November 2026 against Library `545ccb3366b363dc0fe0a6d000b281a88d7c2407`.
The program has two required outputs: a general connected-reductive automorphic
library over number fields, and the global inputs of Henniart's 2000
local-correspondence construction. Neither track is complete.

The registered roadmap
[`henniart-global-automorphic-roadmap-2026-11-02`](</home/taskhub/pilot/literature/Global roadmap- Henniart's local Langlands correspondence and a modern automorphic library (2 November 2026).md>),
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

## 6 November 2026 Henniart Harris datum chain and Brauer completion

Worker 84 verified this continuation against the current Library
`63d0c9b9d2720e646aa7abb360a08988aee052bf`. Since the previous section, the
three remaining Brauer children and two children of the Henniart Harris datum
chain have been accepted and published under `lean.proof@1`. The irreducible
basis was published in `92a7435d25d4da775fd9c410ea9239236a0eec90`, the
character lattice in `8fb2236bacd54b43eeb9b2fabc30476fee771e05`, and the
Brauer aggregate in `8b3ba080b2e8bcecb1612373f236b9ad96423d12`. The common
base was published in `1eb9a9ee0815224a368f8dc58b7d95f024cfff05`, and the
weight-one CM characters in `80f702330eab13242c1eb52eee2757a5d07eb1ba`. For
each of these five proofs, the machine receipt passes Lake build, exact target,
unchanged statement and frozen inputs. Each independent reviewer approved
without qualifications. Worker 84's task inspections show each exact child done,
with a closed completion declaration and no required feedback. As in the
previous section, the completion declaration identifiers come from inspections
with completion records. Every proof and statement file named in this section
has the same SHA-256 in the current Library and in the workspace. Where Worker
84 offered a pair for adoption, it also equals the adoption bundle. No proof
adds a hypothesis or an axiom.

| Theorem | Candidate and authors | Machine, review and integration | Exact child and completion |
| --- | --- | --- | --- |
| Irreducible basis, `Langlands.FiniteRep.VirtualCharacter.irreducibleBasis` (with `faithfulness` and `faithfulnessAndBasis`) in [VirtualCharacterProof.lean](../../Langlands/Representation/Finite/VirtualCharacterProof.lean) ([explanation](../../Langlands/Representation/Finite/VirtualCharacterProof.md)) | `d9358f43-ab6c-4460-addb-30f3a25198e4`; Worker 1429 with Worker 84 | `da3c85f0-3850-4c30-b742-2a6c88e53914`; Reviewer 15408, review `eef6e04c-b7cb-47ba-acf3-0f58f19e3317`; integration `265806b85b4642cba52b276152205a4f` | `6ca4f435-be10-4896-8cb7-2f4dba41cba4`; `904888d8-cad0-49a0-90ed-022995775645` |
| Integral character lattice, `Langlands.FiniteRep.BrauerLattice.characterLattice` in [BrauerLatticeProof.lean](../../Langlands/Representation/Finite/BrauerLatticeProof.lean) ([explanation](../../Langlands/Representation/Finite/BrauerLatticeProof.md)) | `e9b0fd74-0b3e-49c3-96f1-bd44fc561ff1`; Worker 1696 with Worker 84 | `1039e69a-93ea-4eb6-a49e-cfd6ff55d4af`; Reviewer 15523, review `dd07f05e-e4c7-4e9f-842c-255f4589e479`; integration `92571606cb96454dab35d1281f02dec9` | `0bc7a0fe-3ce6-4d62-9c06-51366702058f`; `23088463-a431-4939-b4cd-8aa19c3bb020` |
| Finite Brauer theory, `Langlands.FiniteRep.BrauerTheory.finiteBrauerTheory` (with `spanning`) in [BrauerTheoryProof.lean](../../Langlands/Representation/Finite/BrauerTheoryProof.lean) ([explanation](../../Langlands/Representation/Finite/BrauerTheoryProof.md)) | `8b252ec8-1d97-4113-960d-e6bde09e17bc`; Worker 1696 with Worker 84 | `0c76d1d0-b8aa-4091-82fd-7f4a3834233e`; Reviewer 15737, review `fb50b3a1-228c-48aa-8513-dc3148153688`; integration `e3b26523f0554a6eae5a56e2a3640cc4` | `fc2e1a73-8768-4bfc-a6c4-7f7623548227`; `030b582e-9f24-46af-a64f-bc3c78c822eb` |
| Common CM base for all intermediate fields, `Langlands.Global.henniartCommonBaseRealization.{uF}` in [HenniartCommonBaseRealizationProof.lean](../../Langlands/Global/Arithmetic/HenniartCommonBaseRealizationProof.lean) ([explanation](../../Langlands/Global/Arithmetic/HenniartCommonBaseRealizationProof.md)) | `1ffc94b9-1586-4e85-8e4e-58bf5e0549d7`; Worker 1693 with Worker 84 | `24428a01-1e66-4108-8c87-aae76b870c6e`; Reviewer 15938, review `0a2decb6-11bb-469c-b68f-a55f8dfb4dfb`; integration `6c09b8975a2c4f25974f6302c8fbc922` | `0fca5ad1-a9ba-4c2a-9480-83ec23b8e523`; `14b0444b-3969-4fd7-ac85-928ee019a23d` |
| Conjugate-inverse weight-one CM characters, `Langlands.Global.cmHalfWeightCharacter.{u}` in [CMHalfWeightCharacterProof.lean](../../Langlands/Global/Arithmetic/CMHalfWeightCharacterProof.lean) ([explanation](../../Langlands/Global/Arithmetic/CMHalfWeightCharacterProof.md)) | `8f69c1ed-dcc8-4350-a897-0846c0ed4d05`; Worker 1692 with Worker 1690 | `e0da3d61-6c6d-446c-b3eb-27b882119016`; Reviewer 16167, review `7ec5761a-9622-4d39-a8a5-03ff67cb04be`; integration `b3f8a3524ff347208e99bf5ec40d23c7` | `a6de2478-e39e-494e-9787-4f2cf8dffd07`; `12079593-e7a1-444e-8a09-a11c0c9e25f9` |

The three Brauer proofs complete the finite-group input of Henniart (2000)
§3.7 (p.451). The target pair `Langlands/Representation/Finite/BrauerStatement`
(Lean `b5f0c11f`, Markdown `196495fe`) is unchanged. The irreducible basis
theorem proves `FiniteIrreducibleBasisStatement G`: the linear map sending
integer coefficients on the actual irreducible classes to the corresponding
element of the virtual representation group is bijective.
The same module proves virtual-character faithfulness and the conjunction of
both. The lattice theorem proves `IntegralBrauerCharacterLatticeStatement G`:
the integer span of the characters of inductions of rank-one data equals the
image of the virtual representation group under the character map, as an
equality and not only up to finite index. Its contribution also carries the
seven-module port of the Anthropic FLT Brauer-induction development under
`Langlands/AnthropicFLT`. The aggregate theorem proves
`FiniteBrauerTheoryStatement G` for every finite group `G` in universe `uG`,
the conjunction of all seven conjuncts. Its new conjunct is integral Brauer
spanning (`IntegralBrauerSpanningStatement G`, surjectivity of the expansion in
rank-one inductions), proved from the lattice equality and faithfulness. With
the finite character theory (`e554ecc4`) and the induced character formula
(`49d62ef7`) of the previous section, all five Brauer children are done.

The datum chain makes Harris's Proposition 4.8 hypotheses available on one CM
base field, as Henniart (2000) §§3.3–3.7 requires. Its three statement
candidates are by Worker 84 and are accepted and public under
`lean.statement@1`:

- `0b6450d7-9f46-4f20-9e17-6f93d4ccf172`, module
  `Langlands/Global/Arithmetic/HenniartHarrisDatumStatement` (Lean `86240147`,
  Markdown `7f8d8473`). It defines `Harris.IsPairedPlaceConfiguration`,
  `HarrisDatumCharacterRealizationStatement`,
  `HenniartCommonBaseRealizationStatement` and `HenniartHarrisDatumStatement`.
  Receipt `e8d29972-c90f-4d6b-b561-4de791d4528d`; Reviewer 15603, review
  `0bfcb976-28ca-4b51-98a3-703064e1077c`; integration
  `21ddb08273c84e858240930f10a840a5`, published in
  `86cf8f8984679ba48ded6fa152c55ec38b532d97`.
- `3078146e-d3eb-4a22-af2e-29de1043619c`, module
  `Langlands/Global/Arithmetic/CMHalfWeightCharacterStatement` (Lean
  `28b3371f`, Markdown `feb6a1bc`), defining
  `CMHalfWeightCharacterStatement`. Receipt
  `e671f6f2-d04d-4c1e-9427-5006942baad5`; Reviewer 15580, review
  `ba89e35a-5aa9-419c-abbe-704986d9925b`; integration
  `4e7dec10c7284c6cb7247c14f65ddc17`, published in the same commit.
- `1c45d2e1-2e77-4965-bd68-77fad5d822ff`, module
  `Langlands/Global/Arithmetic/HenniartHarrisDatumReductionStatement` (Lean
  `d5f8e552`, Markdown `d2a90f28`). It defines the two implications
  `HarrisDatumCharacterRealizationOfHalfWeightStatement` and
  `HenniartHarrisDatumOfHalfWeightStatement`, each with
  `CMHalfWeightCharacterStatement` as premise. Receipt
  `795a997f-af2b-4752-9279-32d12e0f6007`; Reviewer 15732, review
  `c87521cc-f62a-464d-be12-50d1b4a06967`; integration
  `01268616cfb9403b8158ea3f28dd5b7b`, published in
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

Three exact revision-1 children of the datum chain remain. Each is `ready`,
with no member and no candidate, at Worker 84's inspection of 6 November 2026.
Worker 84 offers a complete adoption pair or bundle for each. Development checks
against Library `63d0c9b9` had 0 errors and 0 warnings, with only the axioms
`propext`, `Classical.choice` and `Quot.sound`. These checks are neither
acceptance nor review evidence.

- Character realization, child `535dbe80-d5d0-4ead-9309-540860571cac`
  (target `HarrisDatumCharacterRealizationOfHalfWeightStatement`; no formal
  requirement). The bundle has four Lean/Markdown pairs:
  `HarrisDatumArchimedean`, `HarrisDatumLocal`, `HarrisDatumAuxiliary` and
  `HarrisDatumCharacterRealizationProof`. The route multiplies the regular CM
  character of the published `cmRegularUnitPrescription` by a weight-one
  character from the premise when `[E' : E]` is even. The auxiliary character
  comes from the published `auxiliaryCharacterFirstOrder`, and general position
  from the published transport and exact-stabilizer theorems.
- Datum reduction, child `3e15aeb3-a7cb-4420-a362-ca87356b92e2` (target
  `HenniartHarrisDatumOfHalfWeightStatement`; formal requirements: the done
  common-base child `0fca5ad1` and the character-realization child `535dbe80`).
  It applies the common base and then the character realization at universe
  `0`.
- Harris datum, child `790a86c0-4bcc-4e22-85ec-b43d9c0ac9f8` (target
  `HenniartHarrisDatumStatement`; formal requirements: the datum-reduction child
  `3e15aeb3` and the done weight-one child `a6de2478`). Its theorem is the
  reduction applied to `cmHalfWeightCharacter`. Its module also proves the
  unconditional `HarrisDatumCharacterRealizationStatement` as a further named
  theorem, which is not part of the target.

Each child keeps its own independent proof and publication gates. Even when all
three are done, the datum statement keeps the normalized reciprocity family as
a universally quantified hypothesis; it constructs no such family. Harris's
Proposition 4.8 itself (`Langlands.Global.Harris.Proposition48Statement`) and
the Hecke global functional equation
(`Langlands.Global.HeckeGlobalFunctionalEquationStatement`) have no proof in the
current Library. The Galois-side global functional equation, the global
field/tower, H3 and general automorphic obligations remain unchanged.

## 10 November 2026 carry-over and Bernstein–Lapid §§2–3 continuation

Worker 3657 checked this continuation against Library
`e748734106ab2ee9de1cab1eb18a60e59593aac0`. On 8 November 2026 the project was
carried into a new instance. The standing program keeps its identifier and
revision 1 and is now executed by Worker 3657. The parent's shared draft
(carried as revision 1), the shared DAGs and the carried tasks came along with
their identifiers. The previous workers, their candidates and their reviews
stayed behind. In particular, the H1 block child
`205503d3-82c7-4b1a-a4f0-90d02bbe9a2e` was not carried, so the H1 rows of the
earlier sections are historical. Worker 116 of the previous instance has no
identity here and is credited in Markdown only. The earlier sections are not
recertified by this one.

### New public statements and definitions

Each unit below is by Worker 3657, was independently approved with no
qualifications, and was published. Its Lean and Markdown files have the same
SHA-256 in the current Library and in the workspace; the first eight hex
digits are given.

| Unit | Candidate, review and integration | Exact content and boundary |
| --- | --- | --- |
| [QuotientConvolutionKernelStatement](../../Langlands/Analysis/Local/QuotientConvolutionKernelStatement.md) (Lean `fa04d6ef`, Markdown `0afd3790`) | `5e1dcbf1-06d2-4dd3-a8c1-2737266fc7ae`; Reviewer 710, review `9e82f2448d0c47ecb9411e1a30eb9866`; integration `0b52d7ade01b4bdf86dd3c1299027793`, commit `d39b5aee822fe2ad1aadf07861ebd9a4c2df62a8` | `Langlands.QuotientIntegration.QuotientConvolutionKernelStatement`: continuous kernel vectors and the support bound for compactly supported convolutions on a coset space. It restores the target of the lost previous-instance candidate `f33ece2b`. No proof is public. |
| [ContinuationPrincipleStatement](../../Langlands/Analysis/Meromorphic/ContinuationPrincipleStatement.md) (Lean `f656da08`, Markdown `32166d54`) with helper [AnalyticSystems](../../Langlands/Analysis/Meromorphic/AnalyticSystems.md) (Lean `7755ec49`, Markdown `9fa415ac`) | `6a56c6f8-254b-4313-93b0-f0dd321fa336`; Reviewer 767, review `79cef509a0744cd7a45bf5eb320c7252`; integration `3f91df387255439788ae0621dc842dc7`, commit `58a91d4ff65b8d6dcb8aa417bfc63399feb8b4af` | Bernstein–Lapid (BL) §§3.1–3.3 and Theorem 3.3, pp.192–194: weak holomorphy, local common-denominator meromorphy, analytic systems, local finite type. `MeromorphicContinuationPrincipleStatement` is the conjunction of `MeromorphicContinuationHolomorphicStatement` (openness, holomorphy, meromorphy) and `MeromorphicContinuationAnalyticComplementStatement`. No proof is public. |
| [FredholmCriterionStatement](../../Langlands/Analysis/Meromorphic/FredholmCriterionStatement.md) (Lean `cc795a43`, Markdown `227f04f6`) | `4f579dbc-b7e2-41fe-b7f8-701b7b5d08fa`; Reviewer 777, review `c87730e9a8044f7dbef67baff0dbd721`; integration `0d8405f0d9394c0ba178bea92d551b58`, commit `58a91d4ff65b8d6dcb8aa417bfc63399feb8b4af` | BL §3.4, pp.194–195: `FredholmCriterionStatement` (Banach spaces, left invertible modulo compact operators) and `HilbertFredholmCriterionStatement` (Corollary 3.4); their conjunction `FredholmFiniteTypeStatement`. No proof is public. |
| [AdelicComplexParameters](../../Langlands/Global/AdelicComplexParameters.md) (Lean `d7361cb3`, Markdown `39b93e1e`) with helper [LinearCoordinates](../../Langlands/Analysis/Meromorphic/LinearCoordinates.md) (Lean `62b2a9a4`, Markdown `fcc2c206`) | `296a0871-c095-45c6-8e35-d313aa0dcd8c`; Reviewer 935, review `4dc3d6eac1a94d5698c3873b6281774f`; integration `ecc4d1f236a54489bc42741b35d65486`, commit `e748734106ab2ee9de1cab1eb18a60e59593aac0` | BL §2.1, p.190: `ComplexCharacterParameter F G = ℂ ⊗[ℤ] X^*(G)`, its pairing with the existing `RealCharacterDual`, the real part, and `parameterCharacter`, `m ↦ m^λ = exp ⟨λ, characterLog m⟩`. `IsHolomorphicInCoordinatesOn` and `IsMeromorphicInCoordinatesOn` express holomorphy and meromorphy on such parameter spaces in every complex linear coordinate system. Definitions only. |

Candidate `96508769-0050-478d-a756-630855d8bd65` (Worker 3657) is staged and
unreviewed at this check. It formulates the conditions of Mœglin–Waldspurger
I.2.17 for functions on `G(𝔸)` left invariant under an arbitrary subgroup `Γ`
(module `Langlands.Automorphic.GroupSchemeInvariantForms`), for BL's
`𝒜_P` with `Γ = U(𝔸)M(F)`, and states that for `Γ = G(F)` they coincide with
the existing `IsAdelicAutomorphicForm`. It is not credited here.

### Exact proof children published by Worker 3657

Each is a `lean.proof@1` task with environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. Each was `ready` with no member and
no candidate at publication, and Tasks 5376 and 5387 again at Worker 3657's
inspections of 10 November 2026. Task publication divides proof obligations;
it is not proof evidence.

| Task | Exact target | Recorded route or obstacle |
| --- | --- | --- |
| Task 5376, `6d92e6ea-1d66-4a1b-9ff5-fee9d16c8bbb` | `Langlands.Analysis.IntegratedActionConvolutionStatement` | A complete previous-instance proof pair in the parent's shared draft revision 1 (Worker 116) is offered for adoption; its development check `f81ab7c3` had no errors or warnings. |
| Task 5387, `536c7862-9de2-47eb-b906-9a717903923e` | `Langlands.QuotientIntegration.QuotientConvolutionKernelStatement` | Draft revision 1 proof pair (Worker 116) offered; development check `4b0394ad`. |
| Task 5430, `9d78be17-ad9b-4e75-83d9-98e8e7bc7b25` | `Langlands.Analysis.Meromorphic.FredholmFiniteTypeStatement`, with both conjuncts | The pinned Mathlib has Fredholm operators but no lemma that identity minus compact is Fredholm, and no passage from weak to norm holomorphy of operator families. |
| Task 5431, `d952aa50-53d3-411b-a752-c00588a1a8cf` | `Langlands.Analysis.Meromorphic.MeromorphicContinuationHolomorphicStatement` | Holomorphy of compositions needs Hartogs's theorem on separate holomorphy (BL p.193), absent from Mathlib. The identity theorem can replace connectedness of hypersurface complements. |
| Task 5432, `401025cb-76df-4e21-9b2e-70b21d247174` | `Langlands.Analysis.Meromorphic.MeromorphicContinuationAnalyticComplementStatement` | Reducing a possibly infinite family of determinants to finitely many local equations needs the theorem that an arbitrary intersection of analytic subsets is analytic. The statement's Markdown attributes this to Noetherianity of convergent power series; Noetherianity of the local ring alone does not give one common neighborhood. |

The carried proof children of the earlier sections remain open: pointwise
representatives `054d4658-5f9f-4a10-8fdc-135cdf78161d`, invariant subspaces
`21ebd7a6-9d37-4ac3-bf11-95ebfaa3fc9e`, the smooth inverse kernel sequence
`aeb12597-b4d8-492d-ae26-4a9873ec45f3`, the full almost-everywhere finite
approximation `816bc6a1-cfcd-46af-9c34-beb91454151c`, Hecke finite ramification
`9b4e0085-fce3-44d1-9aa8-22d9cf138d51` and Hecke local rigidity
`c9bdc5d6-36b4-4f38-b483-dc509c57ca82`. Each was `ready` without a member at
Worker 3657's inspections of 10 November 2026. Further compact-quotient and
cuspidal proofs in draft revision 1 await these prerequisite proofs before
their own children are published.

### L1/L2 interface agreement

Worker 3657 and Worker 3659 (L1 block `7d827a3e-4245-4c06-ad81-48f413c26faf`)
agreed in their peer conversation on the following division. `𝔞_M` and `H_M`
are the published `RealCharacterDual` and `characterLog`. L1 builds the
Iwasawa height `H_P` for every standard parabolic relative to one supplied
compact `K` with `P(𝔸)K = G(𝔸)`, and the quotient `X_P = U(𝔸)M(F) \ G(𝔸)`.
L2 builds the parameter space and `m ↦ m^λ` (now public), the space `𝒜_P`, the
Eisenstein series, the intertwining operators and the topology of the space of
functions of uniform moderate growth of BL §7. Worker 3659's height module is
staged as candidate `c45ff0d0-8e5e-451d-a14d-a400ad453b0c` and is not
credited here. This agreement is coordination, not a task revision.

Neither track of the program is complete. No L2 continuation, functional
equation or Eisenstein-series statement is public yet, and no Bernstein–Lapid
proof is public.

## 11 November 2026 Bernstein–Lapid §2 statements

Worker 3657 checked this section against Library
`0ef479821d752edef9ef540203ddfb7f637bbce6`. It supersedes the last paragraph of
the previous section: the L2 Eisenstein-series statements below are now public.

### Further public units by Worker 3657

Each unit below was independently approved with no qualifications and
published. Its Lean and Markdown files have the same SHA-256 in the current
Library and in the workspace; the first eight hex digits are given. Helper
modules are listed with the unit that introduced them.

| Unit | Candidate, review and integration | Exact content and boundary |
| --- | --- | --- |
| [GroupSchemeInvariantFormsComparisonStatement](../../Langlands/Automorphic/GroupSchemeInvariantFormsComparisonStatement.md) (Lean `1a189eff`, Markdown `86950803`) with helper [GroupSchemeInvariantForms](../../Langlands/Automorphic/GroupSchemeInvariantForms.md) (Lean `2b274119`, Markdown `c265bd16`) | `96508769-0050-478d-a756-630855d8bd65`; Reviewer 988, review `6a5016e6c77f40c3b21adc67576b5da6`; integration `84a0ca54286046bd954b8d8c94e3f2b9` | Mœglin–Waldspurger (MW) I.2.17 for functions on `G(𝔸)` left invariant under an arbitrary subgroup `Γ` (`IsAutomorphicFunctionOn`); for `Γ = U(𝔸)M(F)` this is BL's `𝒜_P`. The statement asserts agreement with the existing `IsAdelicAutomorphicForm` for `Γ = G(F)`. No proof is public. |
| [GroupSchemeUniformGrowthFrechet](../../Langlands/Automorphic/GroupSchemeUniformGrowthFrechet.md) (Lean `9f230e9c`, Markdown `a38c7bad`) | `447f2be3-65e4-4ba7-9cda-a8a41e212cea` (replaces the rejected `89e18743`); Reviewer 1019, review `30197ed6b01c4cbb93549d09d636daa9`; integration `db3ff8c36c584ae6bb293f8c04e6a043` | Derived from BL §7.1, pp.210–211: the Fréchet space `UniformGrowthFrechetSpace … hN hrho R L` of right `L`-invariant smooth functions of uniform moderate growth with exponent `R`, weighted through a closed matrix embedding `rho`. It agrees with BL's space only up to a change of exponent (explained, not proved, in the Markdown). The LF-topology on `𝔉_umg` is not constructed. Definitions only. |
| [AdelicEisensteinConvergenceStatement](../../Langlands/Global/AdelicEisensteinConvergenceStatement.md) (Lean `2af25eb3`, Markdown `e2c87e54`) with helper [AdelicEisensteinSeries](../../Langlands/Global/AdelicEisensteinSeries.md) (Lean `2d42887f`, Markdown `882ea294`) | `24ad659b-7f19-407e-bff1-b7b45883949f`; Reviewer 1107, review `e2afb5c1e5cb4bcb91f2be2a3427b8d2`; integration `0c582e6c4c4c4b07883e7bfbe263ae35` | BL (2.1), p.191, and MW II.1.5, p.85: `m_P^λ`, `φ_λ`, the series `E(g, φ, λ) = Σ_{P(F)\G(F)} φ_λ(γg)`, the regularity predicate `IsRegularParameter` and `EisensteinAbsoluteConvergenceStatement` (normal convergence for `g` in compacts and `λ` in compacts of a translate of the positive cone). |
| [AdelicEisensteinContinuationStatement](../../Langlands/Global/AdelicEisensteinContinuationStatement.md) (Lean `4c80d8f1`, Markdown `0cebae37`) | `47f657cb-43e4-4115-a422-722b698eccc8`; Reviewer 1167, review `57d99508933f44829a04cc2ab794196f`; integration `677d9b8a88724bbdbfac1eb2b6b07878` | BL Theorem 2.3 (1) in the Fréchet form of the Corollary in §8.6, p.226: `EisensteinMeromorphicContinuationStatement`. |
| [AdelicIntertwiningConvergenceStatement](../../Langlands/Global/AdelicIntertwiningConvergenceStatement.md) (Lean `4721b1ae`, Markdown `716f7ff6`) with helper [AdelicIntertwiningOperator](../../Langlands/Global/AdelicIntertwiningOperator.md) (Lean `96d51eac`, Markdown `6a9201a4`) | `ee2c6c5b-fa92-4cb9-97fa-78a06930a05f`; Reviewer 1171, review `e735bee08e9b4dee8d175cf3ed55de1e`; integration `48ed54b373644e7db3305e0afbd670c8` | MW II.1.6, pp.87–88, and BL §2.2: `w λ`, the Weyl presentation `IsWeylConjugation`, the operator `M(w, λ)φ` on actual adelic points, and `IntertwiningAbsoluteConvergenceStatement` (domination by an integrable function on a region smaller than BL's). |
| [AdelicIntertwiningContinuationStatement](../../Langlands/Global/AdelicIntertwiningContinuationStatement.md) (Lean `aae8f61d`, Markdown `2efc8b0a`) | `98bd46c6-faf3-401f-b69d-cf3bb27d5c07` (replaces the withdrawn `4b5260cd`); Reviewer 1185, review `c23f508f45e049d5aca2ad53765bd95a`; integration `bc12adf0fc3f47cdb275be236c3ec5ff` | BL Theorem 2.3 (3): `M(w, λ)φ` continues meromorphically within a finite-dimensional subspace of `𝒜_Q`. |
| [AdelicEisensteinFunctionalEquationStatement](../../Langlands/Global/AdelicEisensteinFunctionalEquationStatement.md) (Lean `ed392154`, Markdown `ec1e2499`) | `ad7f0786-88ee-48d9-884a-1f449b24a840`; Reviewer 1190, review `ba26241210214c96a096ae1262cfef75`; integration `e902afce33ff4e57b24486e1f94509b4` | BL Theorem 2.3 (4), universal over continuation data: `E(φ, λ) = E(M(w, λ)φ, wλ)` on the intersection of the domains. |
| [AdelicIntertwiningCocycleStatement](../../Langlands/Global/AdelicIntertwiningCocycleStatement.md) (Lean `6816d705`, Markdown `7cf7b05b`) | `f9c5c784-aa6a-4485-9a46-3230b640cce0`; Reviewer 1193, review `acc00cf5021a41c0a7675a12fcb7284a`; integration `3bd550fc23394cbfb49306da917f3ba1` | BL Theorem 2.3 (5), universal over continuation data: `M(w'w, λ) = M(w', wλ) M(w, λ)`. |
| [AdelicRootHyperplaneStatement](../../Langlands/Global/AdelicRootHyperplaneStatement.md) (Lean `93674a47`, Markdown `c3d01c3a`) | `a06fca02-ee20-4b5d-a732-b05b42508026`; Reviewer 1228, review `f1a1b939c9024aa092711cfdf5a2a5aa`; integration `88706ba7ef51470cbfa9b01bb14e470c` | BL Theorem 2.3 (6), first sentence, in the local product form of the Corollary in §8.6: singularities of `M(w, λ)φ` and `E(φ, λ)` lie along root hyperplanes. |

The clause of BL Theorem 2.3 (1) that a regular value of the continuation is
an automorphic form is a conjunct of the continuation statement. BL Theorem
2.3 (2) and the rationality clause of 2.3 (3) concern function fields and are
not formalized; all statements above assume a number field.

### Further proof children published by Worker 3657

Each is a `lean.proof@1` task with environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, ready with no member and no
candidate at publication; Tasks 5490 and 5499 were again so at Worker 3657's
inspection of 11 November 2026. Task publication divides proof obligations; it
is not proof evidence. The routes are recorded in the task contexts.

| Task | Exact target | Recorded route or obstacle |
| --- | --- | --- |
| Task 5466, `53bc6dc5-f87a-41cf-a951-ea16c4a21f5e` | `Langlands.Global.WeilPairPoleRegionStatement` (Henniart 1986, 4.5 (i)) | H1 analytic input. |
| Task 5467, `a000ce99-f691-4f7e-9a02-15e6fe0eebc0` | `Langlands.Global.GLPairPoleRegionStatement` (Henniart 1986, 4.5 (ii)) | Needs Jacquet–Piatetski-Shapiro–Shalika L-factor computations that the Library lacks. |
| Task 5490, `1832dcb1-0d24-4d4b-b194-f272613d96c9` | `Langlands.Global.EisensteinAbsoluteConvergenceStatement` | Moderate growth, comparison of heights on Siegel sets, Godement's convergence of `Σ m_P(γg)^ν`. |
| Task 5499, `1b5b4ce6-41e1-412f-a47c-c378bf0f4bb7` | `Langlands.Global.EisensteinMeromorphicContinuationStatement` | BL §§4–8: the system `Ξ_fnl(λ)`, uniqueness through leading cuspidal components (§6), finite type (§7), and the continuation principle (Tasks 5430–5432). |
| Task 5500, `ab6ff27b-8e0d-4c78-8146-0b971d98acda` | `Langlands.Global.IntertwiningAbsoluteConvergenceStatement` | Unfolding against the normal convergence of the Eisenstein series (MW II.1.6). |
| Task 5501, `c1648848-1e63-45a5-8590-3e61a11b64f1` | `Langlands.Global.IntertwiningMeromorphicContinuationStatement` | Constant terms of the continued Eisenstein series (BL Lemma 6.10, Corollary in §8.6). |
| Task 5502, `f93514cd-a5e8-4481-97e0-5c645b0dd5de` | `Langlands.Global.EisensteinFunctionalEquationStatement` | The `P`-regular and `wλ`-regular regions are in general disjoint, so the identity needs BL's uniqueness through leading terms (§6), not only convergent series. |
| Task 5503, `5f78828a-eded-4b7e-ad4f-722c1648a944` | `Langlands.Global.IntertwiningCocycleStatement` | BL deduce it from 2.3 (4) and injectivity (8.4); a direct Fubini argument covers only pairs whose lengths add. |
| Task 5504, `4edc456b-6a8e-4d8e-aa41-e8c0f1cbf41b` | `Langlands.Global.RootHyperplaneSingularitiesStatement` | BL Corollary in §8.6. |

The shared DAG (revision 186) records these tasks on the nodes
`proof.eisenstein-absolute-convergence` through
`proof.root-hyperplane-singularities`.

Neither track of the program is complete. No Bernstein–Lapid proof is public.
The constant term of Eisenstein series (MW II.1.7, BL Lemma 6.10), the
`W(P, Q)` double-coset bookkeeping beyond single presentations, and the
LF-topology on `𝔉_umg` remain unstated.

## 11 November 2026 constant term of Eisenstein series and the L3 block

Worker 3657 checked this section against Library
`63d9b857523edf47443b7bf30844159e526d00b0`. It supersedes the last paragraph of
the previous section: the constant term of Eisenstein series is now stated.

| Unit | Candidate, review and integration | Exact content and boundary |
| --- | --- | --- |
| [AdelicEisensteinConstantTermStatement](../../Langlands/Global/AdelicEisensteinConstantTermStatement.md) (Lean `a4138f87`, Markdown `add4c81f`) | `b8a2cf26-b09c-497f-a45e-2e47da6c5ba9` (replaces the rejected `4f07fc96`); Reviewer 1444, review `d18c42f42b5b42b6ac84007123ff8b0f`, no qualifications; integration `ec3bc15416e44cb18d5c4240ddedeb62` | BL Lemma 6.10, formula (6.17), pp.208–209, and MW II.1.7, pp.91–93, without cuspidality: `EisensteinConstantTermStatement`. For arbitrary rational double-coset representatives `w_i` of `Q(F)\G(F)/P(F)` and parabolics `P'_i`, `Q'_i` described by their rational points, the constant term of `E(φ, λ)` along `Q` is the sum of the intertwining integrals of the constant terms of `φ` along `P'_i`, with integrability and summability conjuncts. Helpers: `rationalImage`, `RelativeRationalCosets`, `subgroupConstantTerm` (the measure divides by the total mass and is zero at infinite mass), `parameterRestrict`, `IsDoubleCosetRepresentatives`, `IsGeometricLemmaDatum`. Formula (6.18) for the cuspidal projection is not stated. |

Worker 3657 also published two ready tasks with no member:

- Task 5571, `cc4564a0-9a9b-4b0d-a1be-3c4b2bd10509` (`lean.proof@1`, environment
  `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`): prove exactly
  `Langlands.Global.EisensteinConstantTermStatement`. The route is BL's unfolding
  over the given representatives; it needs the absolute convergence of Task 5490.
- Task 5536, `e079aef9-b46a-468b-a373-87322d41b934` (`lean.peer@1`): the L3
  block of parabolic combinatorics (`τ_P`, `τ̂_P`, `σ`, Langlands' `φ_P(Λ, H)`,
  Arthur 1978 Proposition 1.1 and Lemmas 6.1 and 6.3), `(G, M)`-families
  (Arthur 2005, Lemmas 17.1 and 17.4–17.6) and Arthur truncation (Lemma 8.2,
  Propositions 13.1–13.3). The Library had none of these when the task was
  published.

The shared DAG (revision 207) records Task 5571 on the node
`proof.eisenstein-constant-term` and Task 5536 on
`def.arthur-parabolic-combinatorics-truncation`.

Neither track of the program is complete. No Bernstein–Lapid proof is public.
The `W(P, Q)` bookkeeping beyond single presentations, the LF-topology on
`𝔉_umg` and the Lapid 2011 spectral statements remain unstated.

## 11 November 2026 Lapid 2011 Propositions 2 and 6

Worker 3657 checked this section against Library
`4ed6d9794db38a5178b5c7ab6b048b42eff9d907`. It supersedes the last paragraph of
the previous section in one respect: two of the Lapid 2011 spectral statements
are now public. The source is E. Lapid, *On Arthur's asymptotic inner product
formula of truncated Eisenstein series*, Clay Math. Proc. 13 (2011),
pp. 309–331, registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`.

Both units below were independently approved with no qualifications and
published. Their Lean and Markdown files have the same SHA-256 in the current
Library and in the workspace; the first eight hex digits are given. Both are
stated for number fields `F : Type` (universe zero), because the canonical
split-centre interface they use is stated in that universe.

| Unit | Candidate, review and integration | Exact content and boundary |
| --- | --- | --- |
| [AdelicEisensteinImaginaryHolomorphyStatement](../../Langlands/Global/AdelicEisensteinImaginaryHolomorphyStatement.md) (Lean `efcedca0`, Markdown `569743bb`) with helper [AdelicSquareIntegrableInducedForms](../../Langlands/Global/AdelicSquareIntegrableInducedForms.md) (Lean `6550e9c2`, Markdown `c37517a9`) | `14e81d1e-5c1e-4346-ba65-62066df15d85`; Reviewer 1632, review task `ed3b21b6-5765-40bc-9f6b-8ce2cd381abe`; integration `baca339d77ae461d8756569e78bd8a39` | Lapid Proposition 6, pp.329–330, in scalar form: `EisensteinImaginaryAxisHolomorphyStatement`. For every continuation `(E, D)` of the Eisenstein series of a vector of `A^2_P` there is a continuation `(E', D')` with `i𝔞_P^* ⊆ D'`, meromorphic in every `g` on the one domain `D'`, that agrees with `E` on `D ∩ D'`. Helpers: `imaginaryParameter`, `modulusParameter`, `halfModulusParameter` (`ρ_P`), `IsSplitComponentEquivariant` (`A^n_P`) and `IsSquareIntegrableInducedForm` (`A^2_P`). Fréchet-valued holomorphy is not asserted. |
| [AdelicWavePacketInnerProductStatement](../../Langlands/Global/AdelicWavePacketInnerProductStatement.md) (Lean `2e4f68cb`, Markdown `766b310b`) with helper [AdelicInducedInnerProduct](../../Langlands/Global/AdelicInducedInnerProduct.md) (Lean `150e3f0b`, Markdown `ca9be0ab`) | `ca9e63c9-6735-4e6e-b9b5-6347147f0c7d`; Reviewer 1659, review task `b9d33898-4388-4706-8f25-006512430264`; integration `39b19bf6fa554853929b8e4da9633082` | Lapid Proposition 2, pp.313–314: `WavePacketInnerProductStatement`. Wave packets `Θ` of square-integrable inducing data are in `L²(G(F) \ G(𝔸))`, and their inner product is `∫ Σ_{w ∈ Ω(P, P')} (M(w, λ)φ(λ), φ'(wλ))_{P'} dλ`. The data are globally regular: every generating Eisenstein continuation and every intertwining coefficient must be meromorphic on a domain containing all of `i𝔞_P^*`. Helpers: `parameterCoordinates`, `spectralMeasure`, `IsIwasawaCompatibleMeasure`, the `β`-weighted inner product `inducedInnerProduct`, `realWeylParameter` and `weylParameterSet` (`W(𝔞_M, 𝔞_{M'})`). The Hilbert space `L`, the isometry of Lapid Theorem 2 and surjectivity are not stated. |

The integrator recorded a boundary on the second unit. Because it requires
regularity on all of `i𝔞_P^*`, it cannot serve as the input to Lapid's own proof
of Proposition 6. That proof uses Lemma 10: wave packets of bounded measurable
data supported in a compact set on which the Eisenstein series are regular,
with the bound `‖Θ_φ‖² ≤ |Ω| ‖φ‖²_*`. Lemma 10 is not stated yet.

Worker 3657 published two `lean.proof@1` tasks with environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. Each was ready with no member and no
candidate at Worker 3657's inspection of 11 November 2026. Task publication
divides proof obligations; it is not proof evidence.

| Task | Exact target | Recorded route or obstacle |
| --- | --- | --- |
| Task 5612, `711e48e1-89b5-4fc8-a272-904a2f4e4040` | `Langlands.Global.WavePacketInnerProductStatement` | Lapid §8, p.328: Lemma 9 (square integrability through `Λ^T`), Proposition 1 (the asymptotic formula (2) and its ingredients in §§4–7), Lemma 8 on `(G, M)`-families, the constant term of Task 5571, MW I.4.11, and the adjointness of `M(w, λ)`. Truncation belongs to the block of Task 5536. |
| Task 5613, `ccfc4843-fa56-468c-bf2f-811151ff64c8` | `Langlands.Global.EisensteinImaginaryAxisHolomorphyStatement` | Lapid §8, pp.329–330: Lemma 10, then a contradiction at a pole of order `k ≥ 1` along a root hyperplane through a point of `i𝔞_P^*`, comparing the growth of `Θ_φ(x_0)` with the bound (19). Bernstein–Lapid Theorem 2.3 supplies Lapid's Working hypothesis. |

The shared DAG (revision 236) records the definitions on
`def.lapid-square-integrable-induced-forms` and
`def.lapid-induced-inner-product`, and the proof tasks on
`proof.lapid-wave-packet-inner-product` and
`proof.lapid-imaginary-axis-holomorphy`. It plans
`proof.lapid-truncated-asymptotic-inner-product` (Proposition 1),
`proof.lapid-local-wave-packet-bound` (Lemma 10) and
`proof.intertwining-imaginary-unitarity` (unitarity of `M(w, λ)` on
`i𝔞_P^*`, Lapid p.312 and MW IV.3.12). None of these three is stated.

Neither track of the program is complete. No Bernstein–Lapid or Lapid proof is
public. Lapid Proposition 1, Lemma 10 and Theorem 2, the unitarity of
`M(w, λ)` on `i𝔞_P^*`, the `W(P, Q)` bookkeeping beyond single presentations
and the LF-topology on `𝔉_umg` remain unstated.

## 12 November 2026 Lapid Lemma 10 and Theorem 2, unitarity, Delorme completeness, Getz–Hahn 10.5.1 and the spectral transform

Worker 3657 checked this section against Library
`440a690b5471ae33c2209a6ebc4d5b21e3923b60`. It supersedes the last
paragraph of the previous section: Lapid's Lemma 10 and Theorem 2 and the
unitarity of `M(w, λ)` on `i𝔞_P^*` are now public statements. So are
Delorme's completeness theorem, Getz–Hahn Theorem 10.5.1 and the unitary
spectral transform of Arthur's Theorem 7.2 (b).

Every unit below was independently approved with no qualifications and
published. Its Lean and Markdown files have the same SHA-256 in the current
Library and in the workspace; the first eight hex digits are given. All are
stated for number fields `F : Type` and are statements only: no proof is
public.

| Unit | Candidate, review and integration | Exact content and boundary |
| --- | --- | --- |
| [AdelicBoundedWavePacketStatement](../../Langlands/Global/AdelicBoundedWavePacketStatement.md) (Lean `ca1a7ce5`, Markdown `4aea27f4`) | `d8716e75-f49d-4acf-820a-ca7b462466e0`; Reviewer 1876, review task `76871ece`; integration `cab81dd3` | Lapid Lemma 10, §8, p.329: `BoundedWavePacketStatement`, the conjunction of the inner-product formula of Proposition 2 for bounded measurable data supported in a compact set where the Eisenstein series and intertwining coefficients are regular, and the bound `‖Θ_φ‖² ≤ |Ω(P, P)| ∫ (φ(λ), φ(λ))_P dλ`. Lapid's `|Ω|` is replaced by the smaller `|Ω(P, P)|` that his proof gives. |
| [AdelicIntertwiningImaginaryUnitarityStatement](../../Langlands/Global/AdelicIntertwiningImaginaryUnitarityStatement.md) (Lean `fd9a5051`, Markdown `97f0943c`) | `34417b88-c93a-4cb3-b120-2c0dc1a1c601` (replacing the withdrawn `cd204ca2` and the rejected `d9658d5e`); Reviewer 1941, review task `c2e41781`; integration `61ce95b0` | Lapid p.312, Mœglin–Waldspurger IV.1.11 (b), VI.2.1 (i): `IntertwiningImaginaryUnitarityStatement`. If `M(w, λ)v_j = ∑ coeff_{ji}(λ) ψ_{ji}` with `v_j ∈ A^2_P`, `ψ_{ji} ∈ A^2_{P'}` and meromorphic coefficients, there are coefficients holomorphic near `i𝔞_P^*`, giving the same functions, that preserve the inner products `(·,·)_P → (·,·)_{P'}` at imaginary `λ`. The availability of the expansions is a hypothesis. Surjectivity of the Hilbert-space extension is not stated. |
| [AdelicWavePacketIsometryStatement](../../Langlands/Global/AdelicWavePacketIsometryStatement.md) (Lean `b3c50d9a`, Markdown `bc1db1ab`) | `69412587-c213-4d0a-b108-4f56c8d2753e`; Reviewer 1912, review task `367a36fa`; integration `5db55983` | Lapid Theorem 2, p.314; Arthur Theorem 7.2 (b): `WavePacketIsometryStatement`. For a finite family of presented parabolics with Weyl-compatible wave packet data, `‖∑_i n_i⁻¹ Θ_i‖² = ∑_i n_i⁻¹ ∫ (F_i, F_i)_{P_i} dλ` with `n_i = ∑_{i'} |Ω(P_i, P_{i'})|`. The coordinate changes are assumed measure preserving. The Hilbert space `L` and the extension are not stated here (see the transform below). |
| [AdelicWavePacketCompletenessStatement](../../Langlands/Global/AdelicWavePacketCompletenessStatement.md) (Lean `8636846a`, Markdown `e82cdb88`) | `38462cf2-a338-423a-8942-60ceb864e60c`; Reviewer 1928, review task `21c4bfd1`; integration `bb92f45c` | Delorme 2023 Theorem 7.9: `WavePacketCompletenessStatement`. A function in `L²(G(F) \ G(𝔸))` orthogonal to the wave packets of every presented parabolic `P` with `P(𝔸)K = G(𝔸)` vanishes almost everywhere, for `K` with an Iwasawa decomposition for some minimal parabolic. |
| [AdelicSpectralDecompositionStatement](../../Langlands/Global/AdelicSpectralDecompositionStatement.md) (Lean `15723fb2`, Markdown `a109f436`) with helpers [AdelicParabolicSpectrum](../../Langlands/Global/AdelicParabolicSpectrum.md) (Lean `1fd80b54`, Markdown `0623b49b`) and [DiscretePart](../../Langlands/Representation/Unitary/DiscretePart.md) (Lean `ea82f030`, Markdown `90f92d7a`) | `a5d9d92f-0898-4560-9a2b-36615f2ccbf8`; Reviewer 2033, review task `6d5ebe8b`; integration `e3ae2a7b` | Getz–Hahn Theorem 10.5.1 on `[G]`: `SpectralDecompositionStatement`. For each minimal `P₀` with `P₀(𝔸)K = G(𝔸)` and the presented standard parabolics `P ⊇ P₀`, the spaces `L²_P([G])` (`parabolicSpectrum`, the closed span of the wave packets over `i(𝔞_M^G)^*`) are finitely many with dense sum, `L²_G([G])` is the discrete spectrum (`discreteSpectrum`, via `Langlands.Analysis.discretePart`), associate parabolics give equal spaces and non-associate ones orthogonal spaces. The unitary transform itself is the next unit. |
| [AdelicSpectralTransformStatement](../../Langlands/Global/AdelicSpectralTransformStatement.md) (Lean `3cad3b70`, Markdown `91b23aaf`) with helper [AdelicSpectralTransformSpaces](../../Langlands/Global/AdelicSpectralTransformSpaces.md) (Lean `5cd47750`, Markdown `464f192c`) | `ace31339-14a7-42ca-a205-b7c609c08210`; Reviewer 2100, review task `681db1f1`; integration `7bfd3fbe` | Arthur 2005 Theorem 7.2 (b), Getz–Hahn (10.22)–(10.24), on `L²(G(F) \ G(𝔸))`: `SpectralTransformStatement`. With `H_P` the closure of the restrictions of `A^2_P` (`inducedHilbertSpace`), operators `M(w, i e(x))` on `H_P` characterized by the meromorphic expansions (`IsImaginaryIntertwiningOperator`) exist. For every such choice there is a linear isometry from Arthur's space `L̂` of Weyl-compatible families (`symmetricFamilySpace`) that extends `∑_P n_P⁻¹ ∫ E(F_P(λ), λ) dλ` from the dense smooth compactly supported families and has closed, `G(𝔸)`-invariant range. It does not state that the transform intertwines the right regular representation with `I_P(λ, y)`, nor the identification of its range with Getz–Hahn's `L²_𝒫([G])`. |

The reviewers recorded boundaries that remain open. The two decomposition
statements live on different quotients: the transform and Delorme's
completeness on `G(F) \ G(𝔸)` with parameters in `i𝔞_P^*`, and Getz–Hahn
10.5.1 on `[G]` with parameters in `i(𝔞_M^G)^*`. No comparison between them
is stated. Completeness is stated for the packets of all presented
parabolics, including non-standard ones, while 10.5.1 uses standard ones;
the proof of 10.5.1 must bridge this (the contract of Task 5696 records two
routes). The comparison of `inducedHilbertSpace` with Arthur's `H_P` and of
`parabolicSpectrum` with the range of the transform are explanatory, not
proved.

Worker 3657 published six `lean.proof@1` tasks with environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`. Each was ready with no member and no
candidate at Worker 3657's inspection of 12 November 2026. Task publication
divides proof obligations; it is not proof evidence.

| Task | Exact target | Recorded route or obstacle |
| --- | --- | --- |
| Task 5654, `35951340-68d5-4bb0-93c6-daa893cfdad5` | `Langlands.Global.BoundedWavePacketStatement` | Lapid p.329: approximate the data by smooth compactly supported data `φ_n` supported near the regular set, use Proposition 2 under local regularity and the unitarity of `M(w, λ)` to show that `Θ_{φ_n}` is Cauchy, and pass to the limit; the bound follows by Cauchy–Schwarz, unitarity and the invariance of `dλ` under `Ω(P, P)`. |
| Task 5682, `6b05d7a3-a870-4561-be7e-fc588195e1be` | `Langlands.Global.IntertwiningImaginaryUnitarityStatement` | Mœglin–Waldspurger IV.3.12: adjunction II.1.8, the functional equation `M(w⁻¹, wλ)M(w, λ) = 1`, and root-hyperplane singularities for holomorphy. |
| Task 5683, `898a3612-c34a-45e1-a18d-0f266392ff6f` | `Langlands.Global.WavePacketIsometryStatement` | Proposition 2 for each pair, the Weyl compatibility and the counting `∑_i n_i⁻¹ |Ω(P_i, P_{i'})| = 1`. |
| Task 5684, `4d90c143-14a3-4b66-9001-8fc5738508a9` | `Langlands.Global.WavePacketCompletenessStatement` | Delorme §§3–7: Franke temperedness, uniform temperedness of Eisenstein series, Schwartz-space wave packets (Lapid 2013), Bernstein's temperedness of the spectrum, truncated inner products. Separate statement and proof tasks for these ingredients are expected. |
| Task 5696, `5453d037-1d90-4f14-a068-e04f492be43e` | `Langlands.Global.SpectralDecompositionStatement` | Orthogonality from Proposition 2, equality from the functional equation and unitarity, density from Delorme 7.9 transferred to `[G]`, `L²_G = L²_disc` classically. |
| Task 5697, `1e96fe4f-7f1a-4a3d-a8e6-e1f52b01f56a` | `Langlands.Global.SpectralTransformStatement` | Unitarity for the operators, Theorem 2 for the isometry, Delorme Lemma 6.2 symmetrization for density, closedness of isometric images, and right translation through `I_P(λ, y)`. |

The shared DAG (revision 271) records these on
`proof.lapid-local-wave-packet-bound`, `proof.intertwining-imaginary-unitarity`,
`proof.lapid-wave-packet-isometry`, `proof.delorme-wave-packet-completeness`,
`proof.gh-spectral-decomposition` and `proof.gh-unitary-spectral-transform`.

Two L4 statements by Worker 3657 are staged, not public, and receive no
credit here: Getz–Hahn Theorem 11.3.6, the Whittaker expansion of smooth
cuspidal functions of uniform moderate growth on `GL_{r+1}` (candidate
`bf71922d-bb05-4857-8023-f91bf7747c94`), and Getz–Hahn Theorem 11.4.3,
cuspidal multiplicity one for `GL_n` on the full almost-everywhere cuspidal
`L²` space (candidate `6d7791c7-4842-41f3-ad71-0b3f69e3003a`). The L4 table
row "Whittaker and multiplicity" recorded Cogdell 2007 as missing; these
candidates cite Cogdell's 2004 chapter `cogdell-2004-analytic-theory-gln`,
Theorem 1.1, which states the expansion and sketches the same induction.

Neither track of the program is complete. Lapid's Proposition 1 remains
unstated; it waits for the truncation block of Task 5536, which was ready and
unstaffed at this inspection. No L3 proof is public.

## 13 November 2026 carry-over

Worker 3657 checked this section against Library
`ed924aef420de137b4cbaa3b063a3618afcd73fd` on 13 November 2026. On that day
the project was carried into a new TaskHub instance. Tasks, the shared DAGs
and shared drafts were carried. Candidate, review and conversation records of
the earlier instance were not. Carried tasks keep their ids, restart at
revision 1 and now pin environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`.
This replaces the environment `bb168ec3` named for the six proof tasks of the
previous section. The shared DAG revision numbers restarted with the new
instance; revision numbers quoted in earlier sections refer to the earlier
instance.

This section supersedes the last two paragraphs of the previous section. The
two L4 statements that were staged there are now public. So are the abstract
layer of Arthur's combinatorics and Shahidi (1981), Theorem 5.2. Each unit
below is a statement only; no proof of it is public. The Lean and Markdown
SHA-256 values are those in Library `ed924aef`; the first eight hex digits are
given. The candidate, reviewer and publishing commit are copied from the
shared DAG descriptions written before the carry-over. The earlier records
themselves are no longer readable.

| Unit | Publication record | Exact content and boundary |
| --- | --- | --- |
| [GeneralLinearWhittakerExpansionStatement](../../Langlands/Global/GeneralLinearWhittakerExpansionStatement.md) (Lean `848391b5`, Markdown `2c09f07d`) with helper [GeneralLinearGlobalWhittaker](../../Langlands/Global/GeneralLinearGlobalWhittaker.md) (Lean `ad93620e`, Markdown `1833e4de`) | candidate `bf71922d-bb05-4857-8023-f91bf7747c94`, Reviewer 2169, Library `f59009a7` | Getz–Hahn Theorem 11.3.6, Cogdell 2004 Theorem 1.1, Shalika 1974 Theorem 5.9: `Langlands.Global.WhittakerExpansionStatement`. A smooth (finite level, archimedean plot-smooth) cuspidal function of uniform moderate growth on `GL_{r+1}(F) \ GL_{r+1}(𝔸)` is the absolutely convergent sum of its Whittaker function translated over `N_r(F) \ GL_r(F)`, for a nontrivial character `ψ` trivial on `F` and any generic `m`, and the sum of absolute values converges uniformly on compact sets. |
| [GeneralLinearCuspidalMultiplicityOneStatement](../../Langlands/Automorphic/GeneralLinearCuspidalMultiplicityOneStatement.md) (Lean `4839661c`, Markdown `95e6cc3b`) | candidate `6d7791c7-4842-41f3-ad71-0b3f69e3003a`, Reviewer 2192, Library `47820896` | Getz–Hahn Theorem 11.4.3, Shalika 1974 Theorem 5.5: `Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearCuspidalMultiplicityOneStatement`. On the full almost-everywhere cuspidal subspace of `L²` for `GL_n` (`fullAEL2CuspidalSubmodule`), two irreducible closed invariant subspaces related by an equivariant isometric equivalence are equal. Strong multiplicity one (Getz–Hahn 11.7.2) is not stated here. |
| [ArthurCombinatoricsStatement](../../Langlands/LinearAlgebra/ArthurCombinatoricsStatement.md) (Lean `962297e1`, Markdown `b9d9c421`) with definitions [ArthurCombinatorics](../../Langlands/LinearAlgebra/ArthurCombinatorics.md) (Lean `ba5d8d70`, Markdown `5a36e041`) | candidate `6b49f1a9-a18c-494c-be97-547fbf4f5193` (replacing the rejected `3a49b70c`), Reviewer 2248, Library `24a49431` | Arthur 1978 Proposition 1.1, the remark after Corollary 6.2 in relative form, Lemmas 6.1 and 6.3; Arthur 2005 (8.2) and Lemma 8.3: `Langlands.ArthurCombinatorics.ArthurCombinatoricsStatement`, for a finite crystallographic root system over `ℝ` with a Mathlib base. It is the abstract layer only. Reduced root systems only: a Mathlib base excludes type `BC`. The specialization to actual reductive groups is item 1 of Task 5536. |
| [CuspidalPairBoundaryNonvanishingStatement](../../Langlands/Global/Factors/CuspidalPairBoundaryNonvanishingStatement.md) (Lean `c77278fb`, Markdown `0ccee3fb`) | by Worker 3657; its candidate and review records stayed with the earlier instance | Shahidi 1981 Theorem 5.2: `Langlands.Global.CuspidalPairBoundaryNonvanishingStatement`. For actual cuspidal realizations of `GL_(r+1)` and `GL_(t+1)` with unitary central characters and a finite set `S` of finite places containing both exceptional sets, the partial L-function `L^S(s, π × π')` exists as a meromorphic function on `ℂ` given by the unramified Euler product on a right half-plane, and every such function has nonpositive `meromorphicOrderAt` (no zero) at each `1 + iy`. Holomorphy on `Re s = 1`, pole locations and boundedness in vertical strips are not stated. It is the global boundary nonvanishing input that `AppendixPoleCountingStatement.md` and `MeromorphicPoleComparisonStatement.md` assign to this program. |

The public support module
[AdelicMaximalCompactFactors](../../Langlands/Global/AdelicMaximalCompactFactors.md)
(Lean `80c3d54d`, Markdown `bbca71f1`), requested by Worker 3657, proves that a
maximal compact subgroup of `G(𝔸_F)` is the product of maximal compact
subgroups of `G(𝔸_{F,∞})` and `G(𝔸_{F,f})`, and conversely. It is a proof of
an internal lemma, not a source theorem.

Proof tasks, inspected on 13 November 2026. Each is a `lean.proof@1` task with
environment `5c94c648`. Each was ready, with no member and no candidate. Task
publication divides proof obligations; it is not proof evidence.

| Task | Exact target |
| --- | --- |
| Task 5713, `14ffd874-7923-4c8a-8af4-ef3035b3e131` | `Langlands.Global.WhittakerExpansionStatement` |
| Task 5730, `8056abe3-475e-4af1-b12f-ba5556c2c86e` | `Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearCuspidalMultiplicityOneStatement` |
| Task 5768, `4e277fc9-6303-4213-bb44-eaea2babfdc1` | `Langlands.ArthurCombinatorics.ArthurCombinatoricsStatement` (the six conjuncts as separate named theorems) |
| Task 5816, `c325654f-b8fb-4a43-9caf-c147e4ae95f2` (published 13 November 2026) | `Langlands.Global.CuspidalPairBoundaryNonvanishingStatement` |

The six proof tasks of the previous section (Tasks 5654, 5682–5684, 5696 and
5697) and the functional-equation proof Task 5493
(`8e9a5dd6-1b51-4e53-af72-ca2e6d42fe0a`) were carried at revision 1 with
environment `5c94c648`. The L3 foundations block, Task 5536
(`e079aef9-b46a-468b-a373-87322d41b934`), was ready with no member.

The shared DAG (revision 39) records the new proof task on
`proof.shahidi-boundary-nonvanishing`, with planning edges for Shahidi's route
to `proof.eisenstein-meromorphic-continuation`,
`proof.lapid-imaginary-axis-holomorphy` and `proof.gl-whittaker-expansion`,
and from `proof.henniart-local-unitarity`. The other three units are on
`proof.gl-whittaker-expansion`, `proof.gl-cuspidal-multiplicity-one` and
`proof.arthur-combinatorial-lemmas`.

Remaining L4 targets with no public statement in Library `ed924aef`, checked
by searching the Library's Markdown for their Getz–Hahn numbers:

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
cuspidal and isobaric, p.309) have numerical counterparts in the published, unproved
`CuspidalSpectralRigidityStatement` (Jacquet–Shalika II, Theorems 4.2 and
4.4), owned by Workers 35 and 44: its constituent recovery recovers lists of
full cuspidal classes from their Satake spectra outside a finite set, and its
singleton case recovers one class. Its Markdown records that it does not
compare local unramified components or construct actual isobaric
representations. The representation-theoretic forms of 11.7.2 and 11.7.3 are
not stated, and this ledger does not duplicate the numerical ones.

Neither track of the program is complete. Lapid's Proposition 1 remains
unstated; it waits for the truncation block of Task 5536. No L3 or L4 proof
is public.

## 13 November 2026 Getz–Hahn 11.7.1 poles, Lemma 11.8.1 and the H3 reduction

Worker 3657 checked this section against Library
`46cfa5dd149a3809a3f9bf7a5de0d4f51ca2758c` on 13 November 2026. It
supersedes the list of remaining L4 targets at the end of the previous
section: both targets listed there now have public statements. It also
records two H3 units: the pole-comparison input and the reduction of
`CandidateExistenceStatement` to the open global inputs. Each unit below is a
statement only; no proof of it is public. The Lean and Markdown SHA-256 values
are those in Library `46cfa5dd`; the first eight hex digits are given.

| Unit | Publication record | Exact content and boundary |
| --- | --- | --- |
| [CuspidalPairPoleStatement](../../Langlands/Global/Factors/CuspidalPairPoleStatement.md) (Lean `d4ee856b`, Markdown `bffba086`) | candidate `419008e0-a941-41bd-abad-4da1a1be3153`, review task `1cf9e816-62f7-4ca7-ba62-aa532b8dbdfa`, Library `cfedefb6` | Getz–Hahn Theorem 11.7.1, pole part, p.309; Cogdell 2004 Theorems 4.1 and 4.2: `Langlands.Global.CuspidalPairPoleStatement`. For actual cuspidal realizations of `GL_(r+1)` and `GL_(t+1)` that are trivial on the split components `A_GL` of their centres, the finite local pair data and the archimedean standard-module parameters exist. Every completed pair L-function is holomorphic off `{0, 1}` and has at most simple poles at `0` and `1`. It has a pole there exactly when `r = t` and `T` realizes the contragredient of `T'`. It is bounded in vertical strips outside ε-discs about `0` and `1`. The functional equation is the separate published `CuspidalPairGlobalFunctionalEquationStatement`. |
| [CuspidalIsobaricPoleOrderStatement](../../Langlands/Global/Factors/CuspidalIsobaricPoleOrderStatement.md) (Lean `7cf14664`, Markdown `174324d7`) | candidate `f502aeab-9527-42eb-9ea4-261252b2a799`, review task `6cc1966e-fad5-40a1-b891-089d604c420d` (Reviewer 426), Library `cc5aa77f` | Getz–Hahn Lemma 11.8.1, p.312: `Langlands.Global.CuspidalIsobaricPoleOrderStatement`. Take cuspidal `T₀` and `T₁, …, T_k`, each trivial on the split component of its own centre. Then the data and the completed pair L-functions `Λ(s, π₀ × π_i)` exist, and `min(ord_{s=1} ∏ Λ(s, π₀ × π_i), 0) = -m`. Here `m` is the number of `i` with `T_i` realizing the contragredient of `T₀`. The isobaric sum itself is not constructed; the L-function of `π₀ × ⊞ π_i` is the product. The split-centre hypothesis is essential (counterexample in the previous section). |
| [RelativeCertifiedPoleComparisonsStatement](../../Langlands/Global/Factors/RelativeCertifiedPoleComparisonsStatement.md) (Lean `6e7b8782`, Markdown `cc96b98d`) | candidate `c547b7c2-f8de-45a8-ab62-2292a80ec281`, review task `9fe1431c-b4fe-4280-afbd-598fb6fe2318` (Reviewer 530), Library `730bd1f2` | Henniart 2000, Corollaire 2.4 and Lemme 2.8, pp.445–448, derived: `Langlands.Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement`. The published predicate `RelativeCertifiedPoleComparisons F E c v ψ` holds for all Galois extensions `E/F` of number fields, arithmetic fundamental class families `c`, finite places `v` and nontrivial additive characters `ψ` of `F_v`. That is, a `ψ`-self-dual measure exists. For every such measure the certified pair-factor data exist, with regular completed germs agreeing at `0` and both pole formulas. It is the universal form of the hypothesis of the proved `relativePolePairing`. It does not assert that any witnessed generator exists. |
| [HenniartCandidateExistenceReductionStatement](../../Langlands/Correspondence/HenniartCandidateExistenceReductionStatement.md) (Lean `d2cc1785`, Markdown `0552b85c`) | candidate `05b67471-ae21-4102-8456-0a324f99ec4d`, review task `ea1543c6-54c8-4e75-a4f7-75134db756e5` (Reviewer 863), Library `2e46b9ca` | Henniart 2000, §2.7, Théorème 3.1 and §§3.7–3.8, derived: `Langlands.Henniart.CandidateExistenceReductionStatement.{uK, uW, uP, uE, uQ}`. It is an implication with five hypotheses: Harris 1998 Proposition 4.8 (`Proposition48Statement.{uK, 0, 0, 0, uP}`), Henniart's Théorème 2.4 (`AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP}`), local relative class formation (`LocalRelativeClassFormationStatement.{0}`), the pole comparisons above (`.{0, uW, uP}`) and the composite-map statement (`HenniartCompositeMapStatement.{0, uK, uW, uP, uE}`). Its conclusion is `CandidateExistenceStatement.{uK, uW, 0, uE, uQ}`. The automorphic-lattice universe is `0` because the global construction produces number fields in `Type`. The transport to an arbitrary automorphic universe is not part of it; that is Task 5583 (`54bed1a5-c9db-4be3-b59b-e4eb4abb89b8`, Worker 5732). |

Proof tasks, inspected on 13 November 2026. Each is a `lean.proof@1` task with
environment `5c94c648`, published by Worker 3657 under this program. Each was
ready, with no member and no candidate. Task publication divides proof
obligations; it is not proof evidence.

| Task | Exact target and prerequisites named in the contract |
| --- | --- |
| Task 5921, `786d8bc1-6a9b-4fa0-ae6c-89e17489000c` | `Langlands.Global.CuspidalPairPoleStatement`; Cogdell's route through the global Rankin–Selberg integrals and the mirabolic Eisenstein series |
| Task 5978, `fd17a0f9-9ab1-46d6-a8d9-af3587d0fdcd` | `Langlands.Global.CuspidalIsobaricPoleOrderStatement`; Task 5921, Shahidi's nonvanishing (Task 5816), the symmetry of the contragredient relation and additivity of `meromorphicOrderAt` |
| Task 6017, `0f17fd08-105e-4659-b949-42f622d60eaa` | `Langlands.Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement`; Henniart's Théorème 2.4 and Corollaire 2.4 (proof tasks `65c9a94c-af88-4876-baa4-43d78ccd5531` and `6f8aff78-c965-484e-8f71-d3ca86f6d201`), the JPSS and Weil pole formulas, conjugacy of local maps and unitarity of central characters |
| Task 6289, `207f459d-c3ed-4e90-b4e8-c71e0bba6101` | `Langlands.Henniart.CandidateExistenceReductionStatement`, from its five hypotheses and proved Library results only; it also requires a Library repair, below |

Task 6289 includes a repair. In Library `46cfa5dd` the theorem
`Langlands.Automorphic.OperatorRealization.evaluate_toContinuous_smul` is
declared twice, with the same statement, in
`Langlands/Automorphic/CuspidalAdmissible/Reproduction.lean` and in
`Langlands/Automorphic/OperatorScalarCentralCharacter.lean`. The reduction
needs `henniartGlobalization_of_inputs`, whose module imports the first,
together with `associatedCentralCharacter`, whose module imports the second.
So no module can use both until one declaration is removed. Worker 3657 shared
a complete candidate route as the task's draft revision 1. It moves the
theorem to a new module imported by both files and proves the reduction.

Update, 14 November 2026: Task 6289's proof and repair are published. Worker
390 submitted Worker 3657's draft, rechecked over Library `c40a0134`, as
candidate
`79c92440-93ac-4787-921c-1ac6edd613cf`. Reviewer 2712 approved it (review
task `edf18bca-ab64-44a7-8b77-11ef151d13fd`), and it is published in Library
`457e31a2`. `Langlands.Henniart.candidateExistenceReduction` proves
`CandidateExistenceReductionStatement.{uK, uW, uP, uE, uQ}` (module
`Langlands/Correspondence/HenniartCandidateExistenceReductionProof`).
`OperatorRealization.evaluate_toContinuous_smul` is now declared only once,
in the new module `Langlands/Automorphic/OperatorRealizationEvaluation`, and
both former copies are deleted. The reduction is conditional. A Library
search at commit `457e31a2` found no proof of any of its five inputs.

The open inputs of the reduction and their proof tasks, found by TaskHub
search on 13 November 2026:

- Henniart's Théorème 2.4: task `65c9a94c-af88-4876-baa4-43d78ccd5531`;
- the pole comparisons: Task 6017 above;
- the composite-map statement: task `9e23a040-16d7-4a7a-bd9b-35a08938d3c4`
  (Task 5231), an assembly of four published statements with their own proof
  tasks;
- Harris's Proposition 4.8 and `LocalRelativeClassFormationStatement`: the
  searches `Proposition48Statement`, `Harris Proposition 4.8` and
  `LocalRelativeClassFormationStatement` found no proof task for either. Task
  `1b87b965-a232-4c02-a51f-e287f630c549` proves that Harris's Proposition 4.8
  implies `HenniartGlobalizationStatement`; it does not prove the
  proposition.

GH's own proof of Lemma 11.8.1 ("apply Theorem 11.7.1") omits one input. A
zero at `s = 1` of some `Λ(s, π₀ × π_i)` with `π_i ≇ π₀^∨` would lower the
pole order. The statement Markdown (§6) supplies it from the published
Shahidi 1981 Theorem 5.2 (`CuspidalPairBoundaryNonvanishingStatement`).

The shared DAG records the four statements and proof tasks on
`proof.cuspidal-pair-poles`, `proof.cuspidal-isobaric-pole-order`,
`proof.relative-certified-pole-comparisons` and
`proof.henniart-candidate-existence-reduction` (revision 142).

Remaining L4 targets of the program's list. A search of the Library's
Markdown for their Getz–Hahn numbers, and of its Lean for the half-plane
condition `1 ≤ s.re`, found no public statement of:

- the representation-theoretic forms of Getz–Hahn Theorem 10.7.2
  (Jacquet–Shalika 1981, Theorem 4.4), p.287, and of Theorem 11.7.2 and
  Corollary 11.7.3, p.309. Their numerical counterparts are in the published,
  unproved `CuspidalSpectralRigidityStatement` (previous section);
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

H3 is now reduced, by a published statement, to the five inputs above;
neither the reduction nor any of them is proved. No L3 or L4 proof is
public, and neither track of the program is complete.

## 13–14 November 2026 strong multiplicity one, local regularity, inducing-data rigidity, isobaric sums and constituents of induced representations

Worker 3657 checked this section against Library
`39ad1eee1f5962f7803f7298b1798932d7f29192` on 14 November 2026; its Lean files are
those of Library `757a6793`. It updates the list of
remaining L4 targets at the end of the previous section. Of the targets listed
there, these now have public statements: the representation-theoretic forms
of GH Theorems 10.7.2 and 11.7.2, GH Theorem 10.7.5 at the finite places, and
the p-adic case of GH Theorem 11.5.2. These still have none: the
representation-theoretic form of GH Corollary 11.7.3 (strong multiplicity one
for isobaric representations), GH Definition 10.7.6, GH Theorem 10.7.5 at the
infinite places, and the archimedean case of GH Theorem 11.5.2 (see the end of
this section). Each unit below is a statement only; no
proof of it is public. The first eight hex digits of the Lean and Markdown
SHA-256 values in that Library are given.

| Unit | Publication record | Exact content and boundary |
| --- | --- | --- |
| [CuspidalStrongMultiplicityOneStatement](../../Langlands/Global/Factors/CuspidalStrongMultiplicityOneStatement.md) (Lean `4d489576`, Markdown `0ab67e42`) | candidate `9eb06756-2816-4624-a0a3-c371237b13b4` (replaces the rejected `2977b5b5`), review task `bf184ca5` (Reviewer 1477), Library `430cc03f` | Getz–Hahn Theorem 11.7.2, p.309; Jacquet–Shalika 1981 I, Theorem 4.8 and Corollary 4.10: `Langlands.Global.CuspidalStrongMultiplicityOneStatement.{u, uQ}`. Take cuspidal realizations `T`, `T'` of `GL_(r+1)` with spectral presentations whose finite local components are irreducible and admissible. If their finite local classes agree outside a finite set of finite places, then `T.isoClass = T'.isoClass`. Nothing is assumed at the infinite places. The numerical forms (equal Satake spectra) are the singleton cases of `CuspidalSpectralRigidityStatement`. |
| [UnitaryGenericLPolynomialNonvanishingStatement](../../Langlands/Representation/RankinSelberg/UnitaryGenericLPolynomialNonvanishingStatement.md) (Lean `17dd072a`, Markdown `1aec228b`) | candidate `6e3be211-d5d8-4190-a484-e97c4b726a37` (replaces the rejected `28784017`), review task `4acf5f3c` (Reviewer 1505), Library `430cc03f` | Getz–Hahn Theorem 11.5.2, p.305, p-adic case: `Langlands.RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement.{uF, uV, uW}`. For generic (`Whittaker.IsGeneric`) unitarizable representations `π`, `σ` of `GL_(r+1)` and `GL_(t+1)` over a p-adic field, every symmetric L-polynomial `P` of the pair (`IsPadicSymmetricLPolynomial`) satisfies `P(q^(-s)) ≠ 0` for `Re s ≥ 1`, so `L(s, π × σ) = 1/P(q^(-s))` is holomorphic there. The archimedean case (GH cite Barthel–Ramakrishnan 1994, §2) is not stated. |
| [CuspidalInducingDataRigidityStatement](../../Langlands/Global/Factors/CuspidalInducingDataRigidityStatement.md) (Lean `a1b157bf`, Markdown `c3c67f58`) | candidate `d1aebff6-a8a2-49eb-a51c-3d91932ba0e7`, review task `283ba760` (Reviewer 1580), Library `c257f7cc` | Getz–Hahn Theorem 10.7.2, p.287; Jacquet–Shalika 1981 II, Theorem 4.4, p.809: `Langlands.Global.CuspidalInducingDataRigidityStatement.{u, uQ}`. Take two families of cuspidal realizations `T i` of `GL_(m i + 1)` and `T' j` of `GL_(m' j + 1)` with `∑ (m i + 1) = ∑ (m' j + 1) = r + 1`, and presentations irreducible and admissible at every finite place. Suppose that at every finite place outside a finite set the local components are spherical and the two normalized block inductions have a common spherical subquotient. Then a bijection `e` of the index sets matches the full cuspidal classes, with multiplicity. Nothing is assumed at the infinite places. |
| [IsobaricSum](../../Langlands/Representation/Classification/IsobaricSum.md) (Lean `a19e9665`, Markdown `f47811c7`) and [CuspidalIsobaricRealizationStatement](../../Langlands/Global/Factors/CuspidalIsobaricRealizationStatement.md) (Lean `8e18726a`, Markdown `97f6946f`) | candidate `287a6e56-c56e-4843-9de9-841b3d671b48` (replaces the rejected `e3b72c31`), review task `7a9e16b4` (Reviewer 1700), Library `757a6793` | Getz–Hahn Theorem 10.7.5, p.288, at the finite places. `PadicField.TopologicalData.IsIsobaricSum` is the local isobaric sum `π_1 ⊞ ⋯ ⊞ π_k` over a p-adic field, through the Langlands heads of multisegments (Kudla 1994, Theorem 1.2.5). `Langlands.Global.CuspidalIsobaricRealizationStatement.{u, uQ}`: for cuspidal realizations `T i` of `GL_(m i + 1)` with presentations irreducible and admissible at every finite place, there is an irreducible operator subquotient `Q` of rank `r + 1` such that at every finite place `v` the isobaric sum of the `σ_(i,v)` exists, is a subquotient of the normalized block induction, and embeds in the restriction of `Q` to `GL_(r+1)(F_v)`. Not stated: the infinite places, `Q` as a subquotient of the global induced representation, uniqueness, and GH Definition 10.7.6 (a predicate read only at finite places would be too weak; see the statement Markdown, §6). |
| [CuspidalInducedConstituentAutomorphyStatement](../../Langlands/Global/Factors/CuspidalInducedConstituentAutomorphyStatement.md) (Lean `28e55720`, Markdown `df695286`) | candidate `dbd6e833-35d7-4ee5-bffe-cc65cd5c0511`, review task `fbca3c3b` (Reviewer 1783), Library `757a6793` | Getz–Hahn Theorem 10.7.1, first half, pp.286–287; Langlands 1979, Lemma 1 and Proposition 2, pp.203–204 (Getz–Hahn's "appendix to [BJ79]"), at the finite places: `Langlands.Global.CuspidalInducedConstituentAutomorphyStatement.{u, uQ}`. Take cuspidal realizations `T i` of `GL_(m i + 1)` with `∑ (m i + 1) = r + 1` and presentations irreducible and admissible at every finite place. For every finite place `v` let `A v` be an object of the canonical category of `GL_(r+1)(F_v)` that is a subquotient (`IsSubquotientOf`) of the normalized block induction of the `σ_(i,v)`, with a nonzero `GL_(r+1)(O_v)`-fixed vector for `v` outside a finite set. Then one irreducible operator subquotient `Q` of rank `r + 1` receives an injective intertwiner from `A v` into its restriction to `GL_(r+1)(F_v)`, for every finite `v`. Not stated: the infinite places, the converse half of 10.7.1 (every automorphic representation is such a constituent), and `Q` as a constituent of the global induced representation. The isobaric statement above is this statement applied to the local isobaric sums. |

The numerical rigidity that the proofs of the first and third units need is
Worker 44's published `CuspidalSpectralRigidityStatement`
(`Langlands/Automorphic/Unramified/CuspidalSpectralRigidityStatement.lean`,
Library `0123ad79`): Jacquet–Shalika 1981 II, Theorem 4.2 (power-trace
independence of distinct cuspidal classes) and the numerical step of
Theorem 4.4 (recovery of the constituents, with multiplicity, from trace sums
or Euler products). Its recorded owner tasks `91266440` and `6c50b2fd` do not
exist in this instance, and TaskHub search found no proof task for it, so
Worker 3657 published one (Task 6446 below).

Proof tasks. Each is a `lean.proof@1` task with environment `5c94c648`,
published by Worker 3657 under this program. Tasks 6387, 6388, 6446 and 6447
were inspected on 13 November 2026 and Tasks 6519 and 6523 on 14 November
2026; at inspection each was ready, with no member and no candidate. Library
`39ad1eee` contains no proof of any of the six targets, and the staging and
submission-history areas held no candidate for any of these tasks on
14 November 2026. Task publication
divides proof obligations; it is not proof evidence.

| Task | Exact target and prerequisites named in the contract |
| --- | --- |
| Task 6387, `9dcb3206-7035-4d1c-9cea-f620e42f9628` | `UnitaryGenericLPolynomialNonvanishingStatement`; GH's deduction from Proposition 11.5.1: absolute convergence and holomorphy on `Re s ≥ 1` of the local Rankin–Selberg integrals (in equal rank the published, unproved `UnitaryEqualRankConvergenceStatement`), then the proved regularity results for rational continuations and normalized generators |
| Task 6388, `0b0b55d3-ba74-4eea-be8c-03c8b57b3cee` | `CuspidalStrongMultiplicityOneStatement`; GH's route through the pole of `Λ(s, π × π'^∨)` (Task 5921), regularity of the exceptional local factors (Task 6387 at finite places; the archimedean case of GH 11.5.2 is missing from the Library) and a common determinant twist |
| Task 6446, `c4f0be57-1a49-4a42-b813-4354e297ab3f` | `CuspidalSpectralRigidityStatement`; Jacquet–Shalika 1981 II, Theorems 4.1 and 4.2 and the proof of 4.4: absolute convergence for `Re s > 1` (JS I, Lemma 5.2 and Theorem 5.3; not in the Library), the pole at `s = 1` (Task 5921 with Task 6387, or JS II Proposition 3.6), Shahidi's nonvanishing on `Re s = 1` (Task 5816), unitary twists, and the proved `eulerProductTrace` |
| Task 6447, `c6bba40a-b120-420c-9c51-9eae3198c17e` | `CuspidalInducingDataRigidityStatement`; the Satake class of a block induction as the concatenation of the blocks' classes (spherical constituent existence and uniqueness, induction in stages), comparison with the presentations' spectral systems, then the recovery conjunct of Task 6446 |
| Task 6519, `7853bc94-5997-47b3-a5b2-c1607f7c07c9` | `CuspidalInducedConstituentAutomorphyStatement`; Langlands' proof of Proposition 2, pp.205–207: Eisenstein series near a point of the parameter space, their derivatives, Lemmas 7–9 through constant terms along associate parabolics, and Jordan–Hölder. Its analytic input is the Library's general-reductive Eisenstein statements (`Langlands/Global/AdelicEisenstein*`), published but unproved (proof Tasks 5490, 5499, 5500, 5501). Then the easy direction of Lemma 1, a choice of archimedean constituents, and the tensor embedding into an `IrreducibleOperatorSubquotient` |
| Task 6523, `dab321bc-8fad-40cc-bb66-d16b658b075a` | `CuspidalIsobaricRealizationStatement`; local isobaric sums from the proved `multisegmentHeadExhaustion` and `multisegmentHeadExistence`; the isobaric sum as a subquotient of the block induction by induction on the number of blocks from the proved `langlandsHeadProductSubquotient` (Tadić 1986, Proposition A.4(ii)) and induction in stages; sphericity almost everywhere (Getz–Hahn Theorem 10.6.3) through the proved `orderedUnramifiedSphericalGeneration`; then the proof of Task 6519. The local steps do not depend on Task 6519 |


H3 inputs. Worker 0 (Task 0) published two tasks that bear on the five
hypotheses of `CandidateExistenceReductionStatement` (previous section):

- Task 6411, `03546f9b-94c7-4620-b762-48c39652bbff` (`lean.proof@1`): proof
  of `LocalRelativeClassFormationStatement` by projection from the proved
  `localAbsoluteCorestrictionCompatibleClassFormation`. Once public, it
  discharges the third hypothesis.
- Task 6413, `bca10e59-d4e2-40a4-be9b-5d70eaa1acd2`: planning for Harris 1998
  Proposition 4.8 (`Proposition48Statement`). Worker 3657 answered Worker 0
  that this program does not own that proof: the contract treats it as a
  separate deep prerequisite. The reduction uses it at universes
  `{uK, 0, 0, 0, uP}`.

The shared DAG records these units and tasks on
`proof.cuspidal-strong-multiplicity-one`,
`proof.unitary-generic-lpolynomial-nonvanishing`,
`proof.automorphic-rigidity` and `proof.cuspidal-inducing-data-rigidity`
(revision 177), and on `proof.cuspidal-induced-constituent-automorphy` and
`proof.cuspidal-isobaric-realization` (revision 187).

Remaining L4 targets. Still missing from the Library are:

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
  multiplicity from Euler products, is the published, unproved
  `CuspidalSpectralRigidityStatement`. Neither the cuspidal
  `CuspidalStrongMultiplicityOneStatement` nor the finite-place
  `CuspidalIsobaricRealizationStatement` compares two global isobaric
  representations. The corollary first needs the global isobaric interface of
  GH Definition 10.7.6.

No L3 or L4 proof is public, and neither track of the program is complete.

## 14 November 2026 isobaric automorphic representations at every place

Worker 3657 checked this section against Library
`4f6abf4c7e19610e4d89edc9bf64b34ba1db9ff2` on 14 November 2026. It updates the
list of remaining L4 targets at the end of the previous section. Of the targets
listed there, these now have public statements: GH Definition 10.7.6, GH
Theorem 10.7.5 at every place (including the real and complex places), and the
representation-theoretic form of GH Corollary 11.7.3. These still have none:
the archimedean case of GH Theorem 11.5.2, JS I Theorem 5.3, the converse half
of GH Theorem 10.7.1, and GH Corollary 10.7.3. The new units are statements
and definitions only; no proof of either statement is public. The first eight
hex digits of the Lean and Markdown SHA-256 values in that Library are given.

| Unit | Publication record | Exact content and boundary |
| --- | --- | --- |
| [IsobaricAutomorphicRepresentation](../../Langlands/Global/Factors/IsobaricAutomorphicRepresentation.md) (Lean `a5494424`, Markdown `7d320b82`) | candidate `46a6c05a-7ff6-4643-873f-d7bfa9950e99`, review task `71fde1ba` (Reviewer 2124), Library `4f6abf4c` | Getz–Hahn Definition 10.7.6, pp.288–289, with (10.30), p.283, and (10.35), p.288; seven definitions, no theorems. `RealBlock.exponent`, `IsRealLanglandsOrdered` and `IsComplexLanglandsOrdered` order archimedean blocks by weakly decreasing real part of the exponent (GH (10.30)). `OperatorSubquotient.HasRealPlaceLanglandsQuotient v ds` (and the complex analogue) says that the list is in that order and that some `(𝔤_v, K_v)`-map from `realStandardKFinite` of `ds` into the subquotient has nonzero image, irreducible under the compact and Lie actions at `v`. `IrreducibleOperatorSubquotient.IsCuspidalIsobaricSum Q T P h` says: at every finite place `Q` receives an injective intertwiner from an object `A` with `IsIsobaricSum (σ_(i,v)) A`; at every real (complex) place there are parameters `ds i` of the realizations `T i` and a reordering `ds'` of their concatenation with `HasRealPlaceLanglandsQuotient v ds'` (complex analogue). `IsIsobaric Q` is the existence of such cuspidal data. Not asserted: existence or uniqueness of the local data, admissibility of `Q`, invariance under equivalence or change of presentation, and GH's description through the global induced representation. |
| [CuspidalIsobaricAutomorphyStatement](../../Langlands/Global/Factors/CuspidalIsobaricAutomorphyStatement.md) (Lean `f50727e6`, Markdown `a0d2ef91`) | same candidate | Getz–Hahn Theorem 10.7.5, p.288, at every place: `Langlands.Global.CuspidalIsobaricAutomorphyStatement.{u, uQ}`. For cuspidal realizations `T i` of `GL_(m i + 1)` with `∑ (m i + 1) = r + 1` and presentations irreducible and admissible at every finite place, there is `Q : IrreducibleOperatorSubquotient F r` with `Q.IsCuspidalIsobaricSum T P h`. It strengthens the finite-place `CuspidalIsobaricRealizationStatement` at the infinite places but omits that statement's condition that `A` is a subquotient of the local induced representation. Not asserted: `Q` as a subquotient of the global induced representation, and uniqueness. With `k = 1` it implies `CuspidalArchimedeanParameterExistenceStatement`. |
| [IsobaricStrongMultiplicityOneStatement](../../Langlands/Global/Factors/IsobaricStrongMultiplicityOneStatement.md) (Lean `625c1ea5`, Markdown `df75c975`) | same candidate (its entry point) | Getz–Hahn Corollary 11.7.3, p.309 (left as Exercise 11.8): `Langlands.Global.IsobaricStrongMultiplicityOneStatement.{u, uQ}`. For `Q Q' : IrreducibleOperatorSubquotient F r` with `IsIsobaric Q` and `IsIsobaric Q'`, and a finite set `S` of finite places such that at every finite `v ∉ S` one object `A` embeds injectively in both restrictions to `GL_(r+1)(F_v)`, there is a `Q.Equivalence Q'` (finite adelic translations, compact actions and enveloping-algebra actions). The hypothesis says nothing at the infinite places. Not asserted: equality as subquotients, multiplicity one in the space of automorphic forms. |

Proof tasks. Both are `lean.proof@1` tasks with environment `5c94c648`,
published by Worker 3657 under this program on 14 November 2026. At inspection
on 14 November 2026 both were ready, with no member and no candidate. Library
`4f6abf4c` contains no proof of either target, and on that date the staging and
submission-history areas held no candidate for these two tasks or for Tasks
6387, 6388, 6446, 6447, 6519 and 6523 of the previous section.

| Task | Exact target and prerequisites named in the contract |
| --- | --- |
| Task 6553, `a7c52913-89d5-4572-aff4-825141ec529c` | `CuspidalIsobaricAutomorphyStatement`; the finite places as in Task 6523; the archimedean parameters through proofs of `CuspidalArchimedeanParameterExistenceStatement` and its reductions (not named in the contract, but found by search: Task 5720, `a2cfc970`, is a proof task for that statement, and Task 6201, `285d5eab`, one for `RealLanglandsQuotientStatement`); the archimedean case of GH Theorem 10.6.4 (Knapp 1994, Theorems 1 and 4); and an all-places form of GH Theorem 10.7.1 with prescribed archimedean constituents, which is not in the Library (the public `CuspidalInducedConstituentAutomorphyStatement` controls only the finite places) and must be stated and proved in a helper module or through separate tasks |
| Task 6554, `377cdd2a-1281-43b5-bd23-92836e2f056f` | `IsobaricStrongMultiplicityOneStatement`; admissibility of irreducible automorphic subquotients (Borel–Jacquet 1979, Proposition 4.5 and §4.6, p.196) and Flath's factorization including the archimedean `(𝔤, K)`-modules (Flath 1979, Theorem 3, p.181), neither in the Library; `CuspidalInducingDataRigidityStatement` through its proof (Task 6447); independence of the local components from the presentation (not in the Library); uniqueness of local isobaric sums (Kudla Theorem 1.2.5) and of Langlands quotients (Knapp Theorem 1(c), Theorem 4) |

The shared DAG records these units and tasks on
`def.isobaric-automorphic-representation`,
`proof.cuspidal-isobaric-automorphy` and
`proof.isobaric-strong-multiplicity-one` (revision 197).

Remaining L4 targets. Still missing from the Library are:

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

The last four are prerequisites of Tasks 6553 and 6554 that those tasks may
state and prove in helper modules or publish as separate tasks. Library
`4f6abf4c` contains no proof of any statement listed in this section or the
previous one, and neither track of the program is complete.

## 14 November 2026 admissibility of automorphic representations

Worker 3657 checked this section against Library
`c40a01345b2f4172fa41e07ff31644b40e695003` on 14 November 2026. It updates the
list of remaining L4 targets at the end of the previous section: admissibility
of irreducible operator subquotients (Borel–Jacquet 1979, Proposition 4.5 and
§4.6, p.196) now has a public statement, together with Harish-Chandra's
finiteness theorem in the form of Borel–Jacquet §4.3 (i), p.195. The new unit
is one module of definitions and statements; no proof of any of its three
statements is public. Page numbers are printed pages of the registered
Corvallis Part I file `borel-jacquet-1979-automorphic` (printed page = PDF
page + 5). The first eight hex digits of the Lean and Markdown SHA-256 values
in that Library are given.

| Unit | Publication record | Exact content and boundary |
| --- | --- | --- |
| [AutomorphicAdmissibilityStatement](../../Langlands/Automorphic/AutomorphicAdmissibilityStatement.md), definitions (Lean `edb9bd8c`, Markdown `eed56704`) | candidate `556e20bf-d8e6-4cca-b132-fe2afab62864`, review task `5c6c911d` (Reviewer 2461), Library `c40a0134` | Three definitions for `GL_n` over a number field `F`. `centerAnnihilatedForms F n J` is the space of automorphic forms killed by every element of an ideal `J` of `ArchimedeanGL.EnvelopingCenter F n` through `automorphicEnvelopingAction`. `annihilatedFormMultiplicitySpace F n J L σ` is the space of linear maps `φ : (Fin m → ℂ) →ₗ[ℂ] AutomorphicForms F n` that intertwine `σ` with `automorphicCompactRightAction` and take values in the forms fixed by `L` under `automorphicFiniteRightAction` (`jointMultiplicitySpace`) and in `centerAnnihilatedForms F n J`. `OperatorSubquotient.IsJointlyAdmissible Q` is `Langlands.IsJointlyAdmissible Q.finiteRepresentation Q.compactRepresentation`: for every open subgroup `L` of `GL_n(𝔸_f)` and every representation `σ` of `standardInfiniteCompact F n` on `Fin m → ℂ`, the joint multiplicity space of the quotient is finite-dimensional. |
| `HarishChandraFinitenessStatement` (same files) | same candidate | Borel–Jacquet §4.3 (i), p.195, derived there from Harish-Chandra's Theorem 1.7, p.191: `Langlands.Automorphic.HarishChandraFinitenessStatement.{u}`. For every ideal `J` of finite codimension in the center (`Module.Finite ℂ (EnvelopingCenter F n ⧸ J)`), every `L : OpenSubgroup (FiniteAdelicGL F n)` and every `σ` as above, `annihilatedFormMultiplicitySpace F n J L σ` is finite-dimensional. Admissibility is in the Library's Hom form (all finite-dimensional `σ`, all open `L`) instead of Borel–Jacquet's simple idempotents. Not asserted: §4.3 (ii)–(iv), §4.4, anything about square-integrable forms, or groups other than `GL_n`. |
| `GeneratedFormAdmissibilityStatement` (same files) | same candidate | Borel–Jacquet Proposition 4.5, (1) ⇒ (4), p.196: `Langlands.Automorphic.GeneratedFormAdmissibilityStatement.{u}`. For every automorphic form `f`, `generatedFormOperatorRealization F n f` (the Library's form of `f * ℋ`) satisfies `OperatorRealization.IsJointlyAdmissible`. Not asserted: the converse implications (4) ⇒ (3) ⇒ (2) ⇒ (1), or conditions (2) and (3) at single places. |
| `IrreducibleSubquotientAdmissibilityStatement` (same files; entry point of the candidate) | same candidate | The admissibility claim of Borel–Jacquet §4.6, p.196: `Langlands.Automorphic.IrreducibleSubquotientAdmissibilityStatement.{u}`. Every `Q : OperatorSubquotient F n` with `Q.IsIrreducible` satisfies `Q.IsJointlyAdmissible`. Neither cuspidality nor a central character is assumed. Not asserted: any factorization of `Q` into local components, or the comparison of a realization `S` with the subquotient `S/⊥`. |

Relation to earlier Library results. Until this unit the Library had joint
admissibility only for cuspidal realizations with unitary central character
(`cuspidalUnitaryContragredientExistence`, through
`CuspidalAdmissible.isJointlyAdmissible_of_siegelFiniteness` and the proved
`siegelSetGLFiniteness`), and the one-function archimedean finiteness of
Borel–Jacquet Lemma 2.1, p.193
(`ArchimedeanGL.generatedCompactTypeFiniteness`, proved). Neither gives
`HarishChandraFinitenessStatement`, which bounds all automorphic forms of a
given type at once.

Proof tasks. All three are `lean.proof@1` tasks with environment `5c94c648`,
published by Worker 3657 under this program on 14 November 2026 and revised
to revision 2 the same day (context only: sibling task numbers and the
consumer). At inspection on 14 November 2026 all three were ready, with no
member and no candidate, and the staging and submission-history areas held no
candidate for them or for Tasks 6387, 6388, 6446, 6447, 6519, 6523, 6553 and
6554 of the previous two sections.

| Task | Exact target and prerequisites named in the contract |
| --- | --- |
| Task 6609, `38e3fde8-3343-4691-ae61-47e4384823da` | `HarishChandraFinitenessStatement`; route of Borel–Jacquet §4.3: reduction to compact open `L` and to finitely many continuous irreducible `K_∞`-types, finiteness of `GL_n(F)\GL_n(𝔸)/G_∞ L` (§4.3 (2)), and Harish-Chandra's finiteness on `G_∞` for the arithmetic subgroups `Γ_c` (Theorem 1.7, p.191; Harish-Chandra 1968, Chapter I, §2, Theorem 1, p.8, proved in §6). The Library has the cuspidal part of the argument (`CuspidalAdmissible/Reproduction.lean`, `Finiteness.lean`, `JointAdmissibility.lean`) and constant terms (`ConstantTerm.lean`, `GeneralLinearIntrinsicConstantTerm.lean`); the bounds for non-cuspidal forms through their constant terms are not in the Library |
| Task 6610, `b03daed8-a989-47ce-81db-ef575e1c4449` | `GeneratedFormAdmissibilityStatement` through a proof of `HarishChandraFinitenessStatement` (Task 6609); the ideal `J` of finite codimension killing `f` (`isCenterFinite_iff_exists_ideal`), and the fact that `J` kills the whole generated realization, which needs the invariance of the center of the enveloping algebra under `Ad(K_∞)` compatibly with the Library's actions (the contract notes that this compatibility may need to be proved) |
| Task 6611, `31e7c233-a07b-411e-884f-e919222d7c3f` | `IrreducibleSubquotientAdmissibilityStatement` through a proof of `GeneratedFormAdmissibilityStatement` (Task 6610); a cyclic vector `f ∈ Q.upper \ Q.lower` whose generated realization maps onto `Q.Space`; joint admissibility of quotients (averaging over compact open `L`, isotypic projections for `K_∞`); and possibly a lemma comparing `OperatorRealization.IsJointlyAdmissible` with the subquotient form |

The shared DAG records the definitions on `def.automorphic-admissibility` and
the proof tasks on `proof.harish-chandra-finiteness`,
`proof.generated-form-admissibility` and
`proof.irreducible-subquotient-admissibility`, with a consumer edge from
`proof.isobaric-strong-multiplicity-one` (Task 6554, whose route uses
admissibility in its first step) to `proof.irreducible-subquotient-admissibility`
(revision 210).

Remaining L4 targets. Of the list at the end of the previous section, the
admissibility of irreducible operator subquotients is now stated but not
proved. Still missing from the Library as statements are:

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

Library `c40a0134` contains no proof of the target statements of the proof
tasks of this section and the previous two: each of
`HarishChandraFinitenessStatement`,
`GeneratedFormAdmissibilityStatement`,
`IrreducibleSubquotientAdmissibilityStatement`,
`CuspidalIsobaricAutomorphyStatement`,
`IsobaricStrongMultiplicityOneStatement`,
`CuspidalStrongMultiplicityOneStatement`,
`CuspidalSpectralRigidityStatement`,
`CuspidalInducingDataRigidityStatement`,
`CuspidalInducedConstituentAutomorphyStatement`,
`CuspidalIsobaricRealizationStatement` and
`UnitaryGenericLPolynomialNonvanishingStatement` occurs among the Library's
Lean files only in the module that states it (and
`CuspidalIsobaricRealizationStatement` also in a comment of
`CuspidalIsobaricAutomorphyStatement.lean`). Neither track of the program is
complete.

## 14 November 2026 local components, absolute convergence, archimedean Theorem 11.5.2, cuspidal support

Worker 3657 checked this section against Library
`4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86` on 14 November 2026. It records
four units of definitions and statements and the ten proof tasks published
for them. Four items of the list of remaining L4 targets at the end of the
previous section now have public statements: the archimedean case of
Getz–Hahn Theorem 11.5.2, Jacquet–Shalika I Theorem (5.3), and the converse
half of GH Theorem 10.7.1 and GH Corollary 10.7.3, the last two read at the
finite places only. The fourth unit states the existence and uniqueness of
the local components of GH Theorem 6.3.7, read through isotypic restriction
at each place; it does not state Flath's tensor factorization. No proof of any
statement of the four units is public. Page numbers are printed pages; each
unit's Markdown gives the PDF pages of the registered files. The first eight
hex digits of the Lean and Markdown SHA-256 values in that Library are given.

| Unit | Publication record | Exact content and boundary |
| --- | --- | --- |
| [OperatorSubquotientLocalComponentStatement](../../Langlands/Automorphic/OperatorSubquotientLocalComponentStatement.md) (Lean `17165754`, Markdown `894eaec9`) | candidate `08944adf-7faf-461f-aec0-d375241d78e3`, review task `02884966` (Reviewer 2682), Library `4f4af6ba` | Five definitions and three statements for `Q : IrreducibleOperatorSubquotient F r` over a number field `F`, each statement assuming `Q.subquotient.IsJointlyAdmissible`. `Archimedean.gkHoms` is the space of `(𝔤, K)`-module maps and `Archimedean.IsGKIsotypic` says that their ranges span the target. `OperatorSubquotient.IsFinitePlaceIsotypic Q v ρ` says that the ranges of the intertwining maps from `ρ` to `Q.localRepresentation v` span `Q.Space`; `IsRealPlaceIsotypic` and `IsComplexPlaceIsotypic` say the same for the `O(r+1)` or `U(r+1)` translation and the Lie action at one infinite place. `LocalComponentExistenceStatement.{u}` (GH Theorem 6.3.7, p.165, existence of the factors; Flath 1979, Theorem 3, p.181): at every finite place some `A : AutomorphicObject.{u, u} (padicField v) r.succPNat` makes `Q` isotypic, and at every real or complex place some irreducible admissible module satisfying `IsRealGKModule` or `IsComplexGKModule`, on a carrier in `ModuleCat.{u} ℂ`, makes `Q` isotypic. `LocalComponentEmbeddingStatement.{u, uW}` (derived; Flath, p.180): an irreducible local representation makes `Q` isotypic exactly when it has a nonzero intertwining map into the restriction of `Q`. `LocalComponentDeterminationStatement.{u}` (GH Theorem 6.3.7 with the uniqueness of the factors; Flath Theorem 3): `Nonempty (Q.Equivalence Q')` holds exactly when at every place one irreducible local representation makes both `Q` and `Q'` isotypic. Not asserted (Markdown §8): a tensor product isomorphism `Q ≅ ⊗_v π_v` or an `OperatorQuotientTensorPresentation` of `Q`; that almost all components are unramified; genericity or unitarity of the components of cuspidal representations. |
| [CuspidalPairAbsoluteConvergenceStatement](../../Langlands/Global/Factors/CuspidalPairAbsoluteConvergenceStatement.md) (Lean `f18612df`, Markdown `7f9ea458`) | candidate `555aa03d-cb9d-486c-9b61-fcfcac1b1b1f`, review task `826bed23` (Reviewer 2785), Library `4f4af6ba` | One definition and three statements for actual cuspidal realizations with spectral presentations `P`, `P'` and a finite set `S` of finite places containing both exceptional sets. `CuspidalPairAbsoluteConvergence.logEulerTerm P P' hP hP' v n s` is `tr(A_v^k) tr(A'_v^k) q_v^(-ks) / k` with `k = n + 1`. `CuspidalSelfPairContinuationStatement.{u, uQ}` (JS I Lemma (5.2), pp.554–555): if `T` has `HasUnitaryCentralCharacter` and `Td` realizes its contragredient, some `L : ℂ → ℂ` is complex differentiable on `Re s > 1` and, on some right half-plane, is the value of the absolutely convergent product of `partialEulerFactor P Pd hP hPd v s` over `v ∉ S`. `CuspidalPairAbsoluteConvergenceStatement.{u, uQ}` (the entry; JS I Theorem (5.3), p.555, with the double series of its proof, pp.555–557): if `T` and `T'` have unitary central characters and `1 < Re s`, the double series of `‖logEulerTerm P P' hP hP' v n s‖` over `(v, n)` is summable, `∑_(v ∉ S) ‖partialEulerFactor P P' hP hP' v s − 1‖` converges, and the product over `v ∉ S` has value `exp` of the sum of the double series. `CuspidalPairAbsoluteConvergenceReductionStatement.{u, uQ}` is the implication from Lemma (5.2) to Theorem (5.3). Not asserted (Markdown §5): anything on the line `Re s = 1`, meromorphic continuation, poles or growth; holomorphy of `L^S` on `Re s > 1` is not stated separately. |
| [UnitaryGenericPairRegularityStatement](../../Langlands/Representation/Archimedean/UnitaryGenericPairRegularityStatement.md) (Lean `9c1406b8`, Markdown `a2809575`) | candidate `d1329220-e4de-4ead-8dc1-059b4c63153c`, review task `bcc9ed43` (Reviewer 2804), Library `4f4af6ba` | Two predicates and eight statements in namespace `Langlands.Archimedean`. `IsRealUnitarizableGKModule n ρ π` and `IsComplexUnitarizableGKModule n ρ π` ask for a `K`-invariant positive definite Hermitian form (`InvariantPositiveForm ρ`) for which every `X ∈ 𝔤₀` acts by a skew-Hermitian operator (Knapp–Vogan 1995, (0.5), p.6). `RealUnitaryGenericExponentBoundStatement.{uV}` and `ComplexUnitaryGenericExponentBoundStatement.{uV}`: an irreducible admissible generic unitarizable `(𝔤, K)`-module with standard parameter `ds` has `\|realBlockExponent x\| < 1/2` (complex: `\|x.exponent.re\| < 1/2`) for every block `x ∈ ds`. `RealPairLFactorRightHalfPlaneRegularityStatement` and `ComplexPairLFactorRightHalfPlaneRegularityStatement`: if `0 < Re s + realBlockExponent x + realBlockExponent y` for all `x ∈ ds`, `y ∈ ds'` (complex: with `x.exponent.re + y.exponent.re`), the denominator of the pair `L`-factor does not vanish at `s`. `RealUnitaryGenericPairRegularityStatement.{uV, uW}` and `ComplexUnitaryGenericPairRegularityStatement.{uV, uW}` (the entries; GH Theorem 11.5.2, p.305, archimedean case): for two such modules with standard parameters `ds`, `ds'`, `(realPairLFactor ds ds').denominator s ≠ 0` (complex: `complexPairLFactor`) whenever `1 ≤ Re s`. The two reduction statements say that the bounds at `uV` and `uW` and the regularity imply the entry. Not asserted (Markdown, "Correspondence with Getz–Hahn" and "Relation to published statements"): anything for `Re s < 1`; the existence of standard parameters, which are hypotheses; that the archimedean components of unitary cuspidal automorphic representations satisfy the hypotheses. |
| [CuspidalSupportStatement](../../Langlands/Global/Factors/CuspidalSupportStatement.md) (Lean `3d939c62`, Markdown `29637958`) | candidate `bbf49b2c-6d4e-46d3-9986-2a4dbcbe7092`, review task `660f3708` (Reviewer 3171), Library `4f4af6ba`; it replaces the rejected candidate `16acba53`, whose Markdown misstated Langlands' inducing representation on p.205 | One predicate and two statements. `IsFiniteInducedConstituent hm P h Q` asks for `A v : AutomorphicObject.{u, u} (padicField v) r.succPNat` at every finite place and a finite set `S` of finite places such that, at every finite place, `A v` is a subquotient of the normalized induction of the canonical local components of the cuspidal data, `A v` has a nonzero `GL_(r+1)(O_v)`-fixed vector when `v ∉ S`, and `A v` embeds injectively into `Q.subquotient.localRepresentation v`. `CuspidalSupportExistenceStatement.{u}` (the converse half of GH Theorem 10.7.1, pp.286–287; Langlands 1979, Proposition 2, "only if", p.204): every `Q : IrreducibleOperatorSubquotient F r` satisfies the predicate for some cuspidal data with presentations in universe `u`. `CuspidalSupportUniquenessStatement.{u, uQ}` (GH Corollary 10.7.3, p.287): two families of cuspidal data for which the predicate holds for the same `Q` agree up to a bijection `e : Fin k ≃ Fin k'`, with equality in `PositiveRankCuspidalClass F`. Not asserted (Markdown §6): anything at the infinite places, so GH Theorem 10.7.1 at every place is not stated; that `Q` is a constituent of a global induced representation; Langlands' Lemma 1, the admissibility of `Q` or the isotypy of its restrictions; that the spherical condition follows from the other two; a cuspidal-support map to `IsobaricData F`. |

Relation to earlier Library results. Before these units the Library had
finite local components only for cuspidal realizations with a spectral
presentation (`CuspidalAllLocalIrreduciblePresentationExistenceStatement`,
proved) and for operator quotients with a supplied tensor presentation
(`OperatorQuotientTensorPresentation`, which does not assert that one
exists). It had the p-adic case of GH Theorem 11.5.2
(`UnitaryGenericLPolynomialNonvanishingStatement`, stated), convergence of
the partial pair Euler products on some right half-plane (namespace
`CuspidalPairEulerConvergence`), the line `Re s = 1` as the separate
`CuspidalPairBoundaryNonvanishingStatement`, and, of GH §10.7, the first half
of Theorem 10.7.1 (`CuspidalInducedConstituentAutomorphyStatement`) and
Theorem 10.7.2 (`CuspidalInducingDataRigidityStatement`), both stated.

Proof tasks. All ten are `lean.proof@1` tasks with environment `5c94c648`,
published by Worker 3657 under this program on 14 November 2026. Tasks 6815,
6816, 6818, 6819, 6820, 6821 and 6823 were revised to revision 2 the same day
(context only: sibling task numbers in place of forward references, and, for
Tasks 6819 and 6820, the consumer Task 6388 named as the proof task of
`CuspidalStrongMultiplicityOneStatement`). Tasks 6817, 6822 and 6824 are at
revision 1. At inspection on 14 November 2026 all ten were ready, with no
member and no candidate.

| Task | Exact target and prerequisites named in the contract |
| --- | --- |
| Task 6815, `3e10ac73-00ae-4f30-a604-a09968ca2697` | `LocalComponentExistenceStatement`. Route A: at one place, split the operators of `Q` into those at `v` and those away from `v`; on the finite-dimensional fixed-vector subspaces given by joint admissibility, an irreducible module over the tensor product of the two commuting algebras is a tensor product (GH, proof of Theorem 5.7.2 (ii), p.153; Burnside's theorem), which gives the isotypy and a model of the factor inside `Q.Space`. Route B: GH's proof of Theorem 6.3.7, p.166, through Lemma 6.3.6, the proved `flathRestrictedProductExistence` and GH Exercise 4.14. No other unproved Library statement is needed; joint admissibility is a hypothesis |
| Task 6816, `876084f9-496c-4109-818b-291f765e1077` | `LocalComponentEmbeddingStatement`, through a proof of `LocalComponentExistenceStatement` (Task 6815) and semisimple module theory (Mathlib's `isotypicComponent` and `IsIsotypicOfType`), at the infinite places for `(𝔤, K)`-modules; Flath, p.180 |
| Task 6817, `0e6a285c-e06e-4df1-a4d3-fbebc025050d` | `LocalComponentDeterminationStatement`, through proofs of the existence and embedding statements (Tasks 6815 and 6816); for "⇐", the factorization of GH Theorem 6.3.7 (finite part through `flathRestrictedProductExistence`), the independence of restricted tensor products from the reference vectors (`RestrictedTensorReferenceIndependenceStatement`, stated in the Library, not proved), and a criterion for intertwining the operator algebra on subquotients through its generators, which may need to be proved |
| Task 6818, `7825d219-2a04-4194-9e19-95b05a84c4dc` | The four elementary statements `RealPairLFactorRightHalfPlaneRegularityStatement`, `ComplexPairLFactorRightHalfPlaneRegularityStatement`, `RealUnitaryGenericPairRegularityReductionStatement` and `ComplexUnitaryGenericPairRegularityReductionStatement`, from `realLFactor_regular_iff`, `complexLFactor_regular_iff`, additivity of exponents in pair blocks and exponent arithmetic; no unproved Library statement |
| Task 6819, `2adf0aee-a624-473f-bb3e-107c4b182aa4` | `RealUnitaryGenericExponentBoundStatement` (the main work), then `RealUnitaryGenericPairRegularityStatement` from it and Task 6818's proofs. Route: the standard module is irreducible; Knapp–Vogan Theorem 0.6(a), p.7; Badulescu–Renard 2010, Theorems 8.1 and 8.2, p.1131, and Proposition 9.4; uniqueness in the Langlands classification (BR Theorem 3.3; Knapp 1994, Theorem 1). None of these classification theorems is in the Library |
| Task 6820, `7e2316cc-fd6e-4c15-ac95-71edf9e5a50c` | `ComplexUnitaryGenericExponentBoundStatement`, then `ComplexUnitaryGenericPairRegularityStatement` from it and Task 6818's proofs. Route as for Task 6819, with Tadić's classification (BR Theorem 7.2, pp.1129–1131, and Proposition 9.1) and Knapp 1994, Theorem 4; the statement Markdown marks the `GL_n(ℂ)` bound as derived, since BR §8 is written for `GL(n, ℝ)` |
| Task 6821, `1d8cbc81-142d-47eb-9f4d-8b2b13f0fd52` | `CuspidalSelfPairContinuationStatement`. Route A: the global Rankin–Selberg integral for `GL_r × GL_r` with an Eisenstein series (JS I (1.5), (3.17) and (4.6), p.555). Route B: from the published, unproved `CuspidalPairPoleStatement` (GH Theorem 11.7.1, proof Task 5921), after a twist to trivial split centre and division by finitely many local factors |
| Task 6822, `a8e36011-2be8-46cc-a440-0da01109d6e6` | `CuspidalPairAbsoluteConvergenceReductionStatement` (the main work), then `CuspidalPairAbsoluteConvergenceStatement` from it and Task 6821's proof. Route of JS I, pp.555–557: local logarithms (5.3.1) with `UnramifiedUnitary.norm_characterValues_lt_sqrt` (JS I Corollary (2.5)); nonnegative coefficients for the self pair (5.3.3) through `eigenvalues_eq_map_inv_of_isContragredientOf`; Landau's theorem on Dirichlet series with nonnegative coefficients, to be proved with a source; Cauchy–Schwarz (5.3.5); `hasProd_of_summable_norm_sub_one` |
| Task 6823, `63df27ff-5866-4e98-9ae6-650499d82e63` | `CuspidalSupportExistenceStatement`. Route of Langlands 1979, pp.204–205: constant terms along standard block parabolics (Lemma 4), Lemmas 5 and 6 (not in the Library), realization of `Q` in the space of `Ind δ^(-1) σ`, cuspidal blocks with presentations from `cuspidalIrreducibleAdmissibleFiniteSliceExistence`, and Lemma 1, p.203, or `LocalComponentEmbeddingStatement` (once proved) for the embeddings |
| Task 6824, `5c8e59c5-aa00-4b14-9f2a-3762a62c9314` | `CuspidalSupportUniquenessStatement`, through proofs of `IrreducibleSubquotientAdmissibilityStatement` (Task 6611), `LocalComponentExistenceStatement` and `LocalComponentEmbeddingStatement` (Tasks 6815 and 6816) and `CuspidalInducingDataRigidityStatement` (JS II Theorem (4.4), proof Task 6447); the contract does not accept a conditional reduction as the proof |

The shared DAG records the definitions on
`def.operator-subquotient-local-components`,
`def.cuspidal-pair-log-euler-terms`,
`def.archimedean-unitarizable-gk-modules` and
`def.cuspidal-finite-induced-constituent`, and the proof tasks on
`proof.local-component-existence`, `proof.local-component-embedding`,
`proof.local-component-determination`,
`proof.archimedean-pair-regularity-elementary`,
`proof.archimedean-unitary-generic-pair-regularity-real`,
`proof.archimedean-unitary-generic-pair-regularity-complex`,
`proof.cuspidal-self-pair-continuation`,
`proof.cuspidal-pair-absolute-convergence`,
`proof.cuspidal-support-existence` and `proof.cuspidal-support-uniqueness`
(added in revision 230 and present in revision 233). Consumer edges run from
`proof.isobaric-strong-multiplicity-one` (Task 6554) to
`proof.local-component-determination`, from
`proof.cuspidal-strong-multiplicity-one` (Task 6388) to the real and complex
nodes of GH Theorem 11.5.2, and from `proof.automorphic-rigidity` (Task 6446)
to `proof.cuspidal-pair-absolute-convergence`.

Remaining L4 targets. Of the list at the end of the previous section, the
first four items are now stated but not proved, the converse half of GH
Theorem 10.7.1 and GH Corollary 10.7.3 at the finite places only. Still
missing from the Library as statements are:

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
  genericity, a standard parameter), which the route of Task 6388 needs;
  `IsRealUnitarizableGKModule` and `IsComplexUnitarizableGKModule` occur among
  the Library's Lean files only in the module that defines them;
- the cuspidal-support map from irreducible automorphic subquotients to
  `IsobaricData F`.

Library `4f4af6ba` contains no proof of the 16 target statements of this
section's proof tasks, nor of the 11 statements listed at the end of the
previous section: each occurs among the Library's Lean files only in the
module that states it (and `CuspidalIsobaricRealizationStatement` also in
`CuspidalIsobaricAutomorphyStatement.lean`). The staging and
submission-history areas held no proof candidate for any of these 27
statements on 14 November 2026. Outside the stating modules, the only Lean
files there that name one of them are statement candidates for Harris's
Proposition 4.8 (`Langlands/Global/Arithmetic/HarrisProposition48*.lean`,
staging `0588a5db`, `6c7f666b`, `ba721241`, `ee21cbbc` and submission history
`c1d61a23`), which take `CuspidalSpectralRigidityStatement` as a hypothesis.
Neither track of the program is complete.

## 15 November 2026 archimedean components of cuspidal realizations and unitary central characters

Worker 3657 checked this section against Library
`7229bb456a9afe1fc799771f6516c4b5dc9f976b` on 15 November 2026. It records two
statement units and the six proof tasks published for them. Neither unit
introduces a definition. The first states that the standard module of an
archimedean place parameter of an actual cuspidal realization satisfies the
hypotheses of the archimedean case of Getz–Hahn Theorem 11.5.2. It also states
the resulting regularity of the archimedean pair factors on `Re s ≥ 1`. For a
given parameter, this is the fourth item of the list of remaining L4 targets at
the end of the previous section. The second unit derives the normalization
`HasUnitaryCentralCharacter` from `IsTrivialOnSplitCentre`. No proof of any
statement of the two units is public. Page numbers are printed pages; each
unit's Markdown gives the PDF pages of the registered files. The table gives the
first eight hex digits of the Lean and Markdown SHA-256 values in that Library.
Both units were published in Library
`aeb3911c4e1bf6e3a2f653e874e4ebc422d2a61a` (14 November 2026, 23:36 UTC). That is
the integration commit recorded in both accepted artifacts. The four values are
the same there and in the later Libraries `544dba09`, `9243fdc2` and `7229bb45`.

| Unit | Publication record | Exact content and boundary |
| --- | --- | --- |
| [CuspidalArchimedeanComponentStatement](../../Langlands/Automorphic/CuspidalArchimedeanComponentStatement.md) (Lean `716d7244`, Markdown `a234a384`) | candidate `62afe7c5-92fd-4338-94e7-37a832de5a86`, review task `f929fece` (Reviewer 4082), published in Library `aeb3911c`; it replaces the rejected candidate `37be3bc5`, whose Markdown wrongly said that reordering the blocks of an irreducible standard module could give a reducible one | Six statements in namespace `Langlands.Automorphic`, for `T : CuspidalOperatorRealization F r` over a number field `F : Type u` with `CompactSpace (AdeleQuotient F)`. Each component statement assumes a place parameter. `T.realization.HasRealPlaceParameter v ds` gives `realRank ds = r + 1` and an injective map from `realStandardKFinite (r + 1) ds` into the realization that intertwines right translation by `O(r+1)` and right derivatives with the place actions at `v`. `HasComplexPlaceParameter v ds` is the complex analogue. `ArchimedeanStandardAdmissibleStatement` (derived) says that every real and every complex standard module (`realStandardRep n ds`, `complexStandardRep n ds`) is `IsAdmissibleGKModule`, with no rank hypothesis. `CuspidalArchimedeanStandardIrreducibleStatement.{u}`, `CuspidalArchimedeanStandardGenericStatement.{u}` and `CuspidalArchimedeanStandardUnitarizableStatement.{u}` (GH Theorem 11.3.6, p.298, and displays (11.14)–(11.17), pp.300–302) say that the standard module of the parameter is, respectively, `IsIrreducibleGKModule`, `IsRealGenericGKModule` (complex: `IsComplexGenericGKModule`) and `IsRealUnitarizableGKModule` (complex: `IsComplexUnitarizableGKModule`). The unitarizable statement also assumes `HasUnitaryCentralCharacter T`. `CuspidalArchimedeanPairRegularityStatement.{u}` is the entry (GH p.309, before Theorem 11.7.1, through Theorem 11.5.2, p.305). For `T`, `T'` with unitary central characters and parameters `ds`, `ds'` at the same infinite place, it says that `(realPairLFactor ds ds').denominator s ≠ 0` (complex: `complexPairLFactor`) whenever `1 ≤ Re s`. `CuspidalArchimedeanPairRegularityReductionStatement.{u}` says that the four component statements and the archimedean GH 11.5.2 entries at universes `0, 0` imply the entry. Not asserted (Markdown, "What is not asserted"): the existence of parameters, which is `CuspidalArchimedeanParameterExistenceStatement`; isomorphism classes of components beyond the four properties; anything at the finite places or for `Re s < 1`; the identification in Lean of the Library's pair factor with GH's |
| [CuspidalSplitCentreUnitaryStatement](../../Langlands/Global/Factors/CuspidalSplitCentreUnitaryStatement.md) (Lean `bb73c321`, Markdown `30570b48`) | candidate `2e1e9915-55e9-425a-9e49-36a341c08dba`, review task `a3a21bb2` (Reviewer 4091), published in Library `aeb3911c` | One statement, `Langlands.Global.CuspidalSplitCentreUnitaryCentralCharacterStatement.{u}` (derived from GH Lemma 2.6.2, p.69, and Theorem 6.5.3, p.169). For every actual cuspidal realization `T`, `CuspidalPairPoles.IsTrivialOnSplitCentre T` implies `HasUnitaryCentralCharacter T`. The hypothesis is invariance under `a I_(r+1)` for `a ∈ A_(G_m)` (GH (2.20), p.68). The statement links the normalization of `CuspidalPairPoleStatement` and `CuspidalIsobaricPoleOrderStatement` to the hypothesis of `isUnitarizable_of_hasUnitaryCentralCharacter`, of `CuspidalUnitaryLocalUnitarityStatement` and of the unit above. Not asserted (Markdown, "What is not asserted"): the converse, which fails because `\|det\|^(iσ)` with `σ ≠ 0` is unitary and not trivial on `A_GL`; twisting an arbitrary realization to one trivial on `A_GL`; `L²` realizations or square integrability |

Relation to earlier Library results. Before these units the Library already
proved `cuspidalArchimedeanWhittakerFunctional` and
`cuspidalArchimedeanIrreducibleAdmissibleComponent`. The first gives a
Whittaker functional on every nonzero place-stable subspace of a cuspidal
realization. The second gives an irreducible admissible place-stable subspace
at every infinite place. The Library also proved
`isUnitarizable_of_hasUnitaryCentralCharacter`, which gives one invariant
positive form on the whole realization. These three results concern subspaces
of the realization, not the standard module of a given parameter. The Library
stated, without proof, the existence of parameters
(`CuspidalArchimedeanParameterExistenceStatement`; its proof task is Task 5720,
`a2cfc970`, published by another worker), with reductions to local
Langlands-quotient statements (`ArchimedeanParameterReduction`,
`CuspidalArchimedeanGenericComponentReduction`). It also stated the p-adic
analogues `CuspidalUnitaryLocalUnitarityStatement` and
`CuspidalUnitaryLocalGenericityStatement`.
`hasUnitaryCentralCharacter_of_associatedCentralCharacter` derives a unitary
central character from a different hypothesis, an associated Weil-group
representation. We found no lemma in Library `7229bb45` saying that
`realStandardKFinite n ds` is nonzero when `realRank ds = n`, or that
`complexStandardKFinite n ds` is nonzero when `ds.length = n`. If the carrier
were zero, a place parameter would exist for every realization. So the
genericity and irreducibility proofs need this fact, and the contract of
Task 7003 asks for it as a reusable helper.

Proof tasks. All six are `lean.proof@1` tasks with environment `5c94c648`,
published by Worker 3657 under this program on 14 November 2026, all at
revision 1. Each of the five tasks for the archimedean unit names in its context
the sibling tasks published before it by number, and the later ones by statement
name; Task 7005, published last, names all of them by number. These five
contexts also name the consumer Task 6388 (the proof of
`CuspidalStrongMultiplicityOneStatement`) and Task 6998 for the split-centre
step. At inspection on 15 November 2026 all six
were ready, with no member and no candidate.

| Task | Exact target and prerequisites named in the contract |
| --- | --- |
| Task 6998, `2dd46728-358f-4428-b1ee-387f98752a75` | `CuspidalSplitCentreUnitaryCentralCharacterStatement`. Route: the central character `χ` of `T` (`existsUnique_hasCentralCharacter`, `centralCharacter_evaluate`); `χ = 1` on `A_(G_m)`, by evaluating at a point where some function of `T` is nonzero (`exists_evaluate_ne_zero`); every idele is `a · y` with `a ∈ A_(G_m)` and `y` of norm one (GH Lemma 2.6.2, p.69), with `a` built from the infinite ideles and `full_infiniteIdelesInclusion`; `‖χ‖` is trivial on the compact group `NormOneIdeleClasses` (`compactSpace_normOneIdeleClasses`). Only proved Library results are needed; a comparison lemma between the Library's two idele-class quotients may be required |
| Task 6999, `ae8500ea-b349-43af-a409-c33bbccb5317` | `ArchimedeanStandardAdmissibleStatement`. Route: the Iwasawa decomposition `g = diag(a) · u · k` of `GL_n(ℝ)` and `GL_n(ℂ)`, from `exists_upperTriangular_mul_unitary`; a function in the standard module is determined by its restriction to `K`; and `T ↦ (x ↦ (T x)(1))` embeds the intertwiner space into `Module.Dual ℂ (Fin d → ℂ)`. Only Mathlib and proved Library results are needed |
| Task 7000, `f273c02c-55ab-425f-b5d0-c51b0ea23a34` | `CuspidalArchimedeanStandardUnitarizableStatement` and `CuspidalArchimedeanPairRegularityReductionStatement`, each as its own candidate. Unitarizable: pull back the form of `isUnitarizable_of_hasUnitaryCentralCharacter` along the injective map of the parameter. This uses that the place actions at `v` are restrictions of the global compact and real Lie actions (`realPlaceLieAction_apply`, `realPlaceComplexLieInclusion_tmul`). Reduction: apply the archimedean GH 11.5.2 entries at universes `0, 0` with `A = LinearMap.id` (`isRealStandardIntertwiner_id`, `isComplexStandardIntertwining_id`). Only proved Library results are needed; the inputs of the reduction are hypotheses |
| Task 7003, `d785ecd7-e7cc-4174-9da9-68b37467f224` | `CuspidalArchimedeanStandardGenericStatement`, with a new reusable helper module proving `realStandardKFinite n ds ≠ ⊥` when `realRank ds = n` and `complexStandardKFinite n ds ≠ ⊥` when `ds.length = n`. Suggested construction: `f(g) = χδ(b(g)) Φ(k(g))`, with smooth Gram–Schmidt Iwasawa coordinates and a polynomial `Φ`. For an induction block of weight `m`, the `GL_2(ℝ)` raising and lowering operators show that the weights `\|k\| ≥ \|m\| + 1` span a subrepresentation, so the Fourier conditions hold. The image of the parameter is then a nonzero place-stable subspace, `cuspidalArchimedeanWhittakerFunctional` gives a Whittaker functional on it, and the pullback of that functional is the required one |
| Task 7004, `c77dc5a4-25c6-4498-bc30-ecfbcf470106` | `CuspidalArchimedeanStandardIrreducibleStatement`, the deep statement of the unit. Route: nontriviality from Task 7003's helper. Isotypy of the realization at `v`: translates of the component given by `cuspidalArchimedeanIrreducibleAdmissibleComponent` under the operators away from `v`, which commute with the place actions as in `PlaceComponentExistence`, so the standard module is `W₀^(J)`. Multiplicity one, `\|J\| = 1`: either through BR Remark 2.3, Proposition 2.4 and Theorem 3.3(i), pp.1123–1125, with finite length from admissibility (Task 6999), or through a `K`-type of multiplicity one. The BR classification is not in the Library; the contract asks for a separate statement-and-proof task for any large missing input |
| Task 7005, `1a9d552f-6429-45fa-afcd-7f2806c4312f` | `CuspidalArchimedeanPairRegularityStatement`. It assembles the proof of the reduction (Task 7000) with proofs of the reduction's six hypotheses: Tasks 6999, 7004, 7003 and 7000, and the archimedean GH 11.5.2 entries of Tasks 6819 and 6820, which rest on Task 6818. The contract says to start only when those proofs are published |

The shared DAG records the proof tasks on
`proof.cuspidal-split-centre-unitary-central-character`,
`proof.archimedean-standard-module-admissible`,
`proof.cuspidal-archimedean-standard-generic`,
`proof.cuspidal-archimedean-standard-irreducible`,
`proof.cuspidal-archimedean-standard-unitarizable`,
`proof.cuspidal-archimedean-pair-regularity-reduction` and
`proof.cuspidal-archimedean-pair-regularity`. They were added in revision 251,
the current revision on 15 November 2026. There is no new definition node,
because the units define nothing. Besides edges to the definition nodes they
use and to the nodes of the proved Library results named above, edges run from
the irreducibility node to the admissibility node and to the genericity node
(for the nontriviality helper), and from the entry node to the reduction node,
to the four component nodes and to the real and complex nodes of GH Theorem
11.5.2. Consumer edges run from `proof.cuspidal-strong-multiplicity-one`
(Task 6388) to `proof.cuspidal-archimedean-pair-regularity` and to
`proof.cuspidal-split-centre-unitary-central-character`.

Remaining L4 targets. The fourth item of the list at the end of the previous
section is now stated, for the standard module of a given place parameter, but
not proved. That item asks that the archimedean components of a unitary
cuspidal realization satisfy the hypotheses of the archimedean statements. The
existence of a parameter is the separate
`CuspidalArchimedeanParameterExistenceStatement` (Task 5720).
`IsRealUnitarizableGKModule` and `IsComplexUnitarizableGKModule` now also occur
in `CuspidalArchimedeanComponentStatement.lean`. Still missing from the Library
as statements are:

- GH Theorem 10.7.1 at every place (Langlands 1979, Lemma 1 and
  Proposition 2, pp.203–204);
- Flath's factorization of irreducible admissible representations of
  `GL_n(𝔸_F)` with the archimedean `(𝔤, K)`-modules, as a tensor product
  isomorphism (Flath 1979, Theorem 3, p.181); the contract of Task 7004 asks
  for the isotypy at one infinite place as a helper, which is a part of it;
- the cuspidal-support map from irreducible automorphic subquotients to
  `IsobaricData F`.

Correction to the earlier lists. The lists of remaining L4 targets at the end
of the three sections dated 14 November 2026 ("isobaric automorphic
representations at every place", "admissibility of automorphic
representations" and "local components, absolute convergence, archimedean
Theorem 11.5.2, cuspidal support") name the independence of the finite local
components of a cuspidal realization from its spectral presentation. That item
is now proved for irreducible components, so the list above omits it. The proof
was in none of the Libraries `4f6abf4c`, `c40a0134` and `4f4af6ba` against
which those sections were checked; it is in Library `7229bb45`. Module
`Langlands.Automorphic.AssociatedPresentationComparison` (Worker 1679, a
supporting module of Task 5003) proves, among other results, three theorems in namespace
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
`wiki/README.md`. Library `7229bb45` contains no proof of the seven target
statements of this section's proof tasks: each occurs among the Library's Lean
files only in the module that states it. The staging and submission-history
areas held no proof candidate for any of these seven statements on 15 November
2026. The only other Lean
file there that names one of them is the rejected statement candidate
`37be3bc5` in submission history.
Neither track of the program is complete.

## 15 November 2026 cuspidal support at every place

Worker 3657 checked this section against Library
`fab9caeae532b7a65e67e702bcab72d3194371ae` on 15 November 2026. It records one
statement unit of this program, the four proof tasks published for it, a
revision of Task 6999 and a related result of another worker. The unit states
two of the three items of the list of remaining L4 targets at the end of the
previous section, GH Theorem 10.7.1 at every place and the cuspidal-support
map, and also the cuspidal support of isobaric sums. No proof of
any statement of the unit is public. Page numbers are printed pages; the unit's
Markdown gives the PDF pages of the registered files. The table gives the first
eight hex digits of the Lean and Markdown SHA-256 values in that Library. The
unit was published in Library `fab9caea`, the integration commit recorded in
the accepted artifact (base Library `2b8ae82e`).

| Unit | Publication record | Exact content and boundary |
| --- | --- | --- |
| [CuspidalSupportEveryPlaceStatement](../../Langlands/Global/Factors/CuspidalSupportEveryPlaceStatement.md) (Lean `da6078fb`, Markdown `ef1ec7b9`) | candidate `b7bc86db-20ff-4197-a505-c725bf1b1416`, review task `c21bb5ec` (Reviewer 4255), published in Library `fab9caea` | Four definitions and four statements, for a number field `F : Type u` with `CompactSpace (AdeleQuotient F)` and `Q : IrreducibleOperatorSubquotient F r`. `OperatorSubquotient.HasRealPlaceStandardConstituent v ds` (complex: `HasComplexPlaceStandardConstituent`) says that the blocks `ds` have total rank `n` and that some subspace `W` of `realStandardKFinite n ds`, stable under right translation by `O(n)` and right derivatives, maps linearly into `Q` intertwining these with the place actions at `v`, with nonzero image that has no other stable subspaces than `0` and itself. `Langlands.Global.IsInducedConstituent hm P h Q` for cuspidal data `T i` of `GL_(m i + 1)` with `∑ (m i + 1) = r + 1` is `IsFiniteInducedConstituent hm P h Q` together with, at every real (complex) place, parameters `ds i` of the `T i` (`HasRealPlaceParameter`, `HasComplexPlaceParameter`) such that `Q` has a standard constituent at `v` for `(List.ofFn ds).flatten`. `IrreducibleOperatorSubquotient.HasCuspidalSupport D`, for `D : IsobaricData F`, says that `Q` is an induced constituent of cuspidal data whose classes `⟨m i, (T i).isoClass⟩` form `D`. `CuspidalSupportEveryPlaceStatement.{u}` (Langlands 1979, Proposition 2, p.204, and Lemma 1, p.203; GH Theorem 10.7.1, pp.286–287): every `Q` is an induced constituent of some cuspidal data with presentations in universe `u`. `CuspidalSupportDataStatement.{u}` (GH Theorem 10.7.1, Corollary 10.7.3 and the sentence after it, p.287): every `Q` has exactly one `D` with `Q.HasCuspidalSupport.{u, u} D`. `CuspidalSupportDataReductionStatement.{u}`: `CuspidalSupportEveryPlaceStatement.{u}` and `CuspidalSupportUniquenessStatement.{u, u}` imply `CuspidalSupportDataStatement.{u}`. `CuspidalIsobaricSupportStatement.{u, uQ}` (GH Theorem 10.7.5 and (10.35), p.288): if `Q.IsCuspidalIsobaricSum T P h`, then `IsInducedConstituent hm P h Q`. Not asserted (Markdown §6): the first half of GH Theorem 10.7.1 at the infinite places; Langlands' Lemma 1, Flath's factorization, admissibility or isotypy of `Q`; independence of the predicates of the block order or the choice of parameters; that `Q` is determined by its cuspidal support; the converse of the isobaric statement; groups other than `GL_n` |

Relation to earlier Library results. The finite-place forms
`CuspidalSupportExistenceStatement` and `CuspidalSupportUniquenessStatement`
(module `Langlands.Global.Factors.CuspidalSupportStatement`, proof Tasks 6823
and 6824) were already stated. The first conjunct of `IsInducedConstituent` is
`IsFiniteInducedConstituent`, so uniqueness at the finite places is the only
uniqueness input of the reduction. The existence of isobaric sums at every
place is `CuspidalIsobaricAutomorphyStatement` (Task 6553); with
`CuspidalIsobaricSupportStatement` such a sum has the multiset of its summands'
classes as cuspidal support, by the definition of `HasCuspidalSupport`. The
module does not import `OperatorSubquotientLocalComponentStatement`; its
Markdown §3 uses that module only to explain the archimedean predicates.

Proof tasks. All four are `lean.proof@1` tasks with environment `5c94c648`,
published by Worker 3657 under this program on 15 November 2026, all at
revision 1, in the order of the table. Each context names the sibling tasks
published before it by number and the later ones by statement name; Task 7046,
published last, names all of them by number. Each context also names the
finite-place proof Tasks 6823 and 6824 and the related Tasks 5720, 6523, 6553,
6611, 6815–6817 and 7004. At inspection on 15 November 2026 all four were
ready, with no member and no candidate.

| Task | Exact target and prerequisites named in the contract |
| --- | --- |
| Task 7038, `77a8a491-bc89-4cd8-ad39-99a4c66876f9` | `CuspidalSupportDataReductionStatement`. Route: existence from the witness data of the first hypothesis, with the multiset equation by `rfl`; uniqueness from the bijection `e` of index sets given by the second hypothesis applied to the finite conjuncts, then `Multiset.map_map` and `Multiset.map_univ_val_equiv`. Both inputs are hypotheses |
| Task 7041, `cf08cce7-03fe-4cca-b3a8-afe60b7abd6e` | `CuspidalSupportEveryPlaceStatement`, the deep statement of the unit. Route: Langlands' global realization of `Q` as a quotient of a subspace of `Ind δ^(-1) σ` with cuspidal blocks (Lemmas 4–6, pp.204–205), built once as a helper; the finite places as in Task 6823; at an infinite place, parameters of the blocks (`CuspidalArchimedeanParameterExistenceStatement`, Task 5720), irreducibility of their standard modules (Task 7004) and isotypy of local restrictions; the `K_v`-finite induced space as `I((List.ofFn ds).flatten) ⊗ M` by induction in stages; and an irreducible `(𝔤_v, K_v)`-submodule `J` of `Q` (Tasks 6611 and 6815–6817) written as `W / W'` through a flag with one-dimensional steps in a finite-dimensional part of `M`. Langlands' Lemmas 5 and 6, the factorization of the global induced space and the archimedean isotypy of cuspidal realizations are not in the Library; the contract asks for them as helper modules or separate tasks |
| Task 7042, `e0ef179f-a250-4cfe-9377-915668c868a0` | `CuspidalIsobaricSupportStatement`. Route: at the finite places, the local isobaric sum is a subquotient of `canonicalNormalizedProductInduced` (Tadić Proposition A.4(ii), proved as `langlandsHeadProductSubquotient`; step 2 of the contract of Task 6523), with sphericity outside `S` by GH Theorem 10.6.3; at the real and complex places, the Langlands quotient of the standard module of the reordered blocks is a subquotient of `I((List.ofFn ds).flatten)`, because standard modules of reordered blocks have the same composition factors (BR Remark 2.3 and Proposition 2.4, pp.1123–1124). Finite length and the Grothendieck group of archimedean standard modules are not in the Library |
| Task 7046, `0572bce6-6824-4c50-bf51-f823c1f2f6cb` | `CuspidalSupportDataStatement`, the entry point. It applies the proof of the reduction (Task 7038) to proofs of `CuspidalSupportEveryPlaceStatement` (Task 7041) and `CuspidalSupportUniquenessStatement` (Task 6824). The contract says to start only when those proofs are published |

Revision of Task 6999 and the real admissibility proof. Worker 5220 (Task
6749) published module `Langlands.Representation.Archimedean.RealStandardModuleAdmissible`
(Lean `fb22bfba`, Markdown `3e7065d0`; candidate
`5d395c01-3e38-484c-a73f-4a9da6ad00c8`, review task `1f717b34` (Reviewer 4316),
integration commit `fab9caea`, the same Library as the unit above). It proves
`Langlands.Archimedean.realStandardAdmissible : RealStandardAdmissibleStatement`,
where `RealStandardAdmissibleStatement` is `∀ (n : ℕ) (ds : List RealBlock),
IsAdmissibleGKModule (realStandardRep n ds)`. That is the first conjunct of
`ArchimedeanStandardAdmissibleStatement`, the target of Task 6999 (previous
section). The proof follows the route of Task 6999's contract: the Iwasawa
decomposition `exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact`,
determination by the restriction to `O(n)`, and the injective evaluation map
`gkIntertwinerValueAtOne`; the helpers `finrank_gkIntertwiners_kFiniteRep_le`
and `isAdmissibleGKModule_kFiniteRep` hold for any right-translation-stable
subspace of a real principal series. On 15 November 2026 Worker 3657 revised
Task 6999 to revision 2 (contract `e89c51bc`). Only the context changed: it now
names this module and its helpers, so that only the complex conjunct
(`complexStandardRep`, `U(n)`) remains for an executor. The objective, title,
inputs and acceptance policy are unchanged; the task had no member and no
candidate. `ArchimedeanStandardAdmissibleStatement` itself is still unproved
in Library `fab9caea`.

The shared DAG records the unit on the definition node
`def.cuspidal-every-place-induced-constituent` and the proof nodes
`proof.cuspidal-support-data-reduction`, `proof.cuspidal-support-every-place`,
`proof.cuspidal-isobaric-support` and `proof.cuspidal-support-data`, added in
revision 259, the current revision on 15 November 2026. The definition node
has edges to `def.cuspidal-finite-induced-constituent`,
`def.automorphic-archimedean-place-parameter`,
`def.archimedean-standard-module-parameters`,
`def.automorphic-subquotient-place-actions` and `def.isobaric-data`. Edges run
from the every-place node to the nodes of the finite-place existence proof, of
the parameter existence, of the irreducibility of standard modules, of the
local-component existence and embedding, of admissibility and of the finite
slices; from the isobaric node to `def.isobaric-automorphic-representation`;
and from the entry node to the reduction, every-place and finite-place
uniqueness nodes. The same revision adds the real admissibility proof to the
description of `proof.archimedean-standard-module-admissible`.

Remaining L4 targets. The first and third items of the list at the end of the
previous section (GH Theorem 10.7.1 at every place and the cuspidal-support
map) are now stated, but not proved. Still missing from the Library as a
statement is Flath's factorization of irreducible admissible representations
of `GL_n(𝔸_F)` with the archimedean `(𝔤, K)`-modules, as a tensor product
isomorphism (Flath 1979, Theorem 3, p.181). Library `fab9caea` contains no
proof of the four target statements of this section's proof tasks: each occurs
among the Library's Lean files only in the module that states it. The staging
and submission-history areas held no Lean file naming any of them on
15 November 2026.
Neither track of the program is complete.

## 15 November 2026 shared proof drafts on the program's proof tasks

Worker 3657 checked this section against Library
`72480b70c88adff84a438bd7029d64ee3977469c` on 15 November 2026. It records the
drafts that Worker 3657 shared on proof tasks published by this program. A shared draft is a TaskHub draft revision with status
"unreviewed". It is not a candidate: it has no machine validation and no
review, and none of its content is public. At Worker 3657's latest
inspection of each task (13–15 November 2026), none of the tasks below had a
member. A draft becomes a candidate only when an executor of the
task submits it. The draft revisions are under `drafts/<task id>/` in the
project, and the table gives the revision and the first eight hex digits of
its content key. "Check" is the identifier of Worker 3657's own `lean_check`
run in the pinned environment `5c94c648`; the complete drafts were rechecked
on 15 November 2026. The check records are in Worker 3657's private workspace. They are Worker 3657's own report, not
public evidence. Every main theorem below uses only
the axioms `propext`, `Classical.choice` and `Quot.sound`. Library `72480b70`
contains no proof of any target or input statement named in this section:
outside statement modules (files named `…Statement.lean` or
`…Statements.lean`), no Lean file of the Library names any of them, except two
imports of the module of `CuspidalPairBoundaryNonvanishingStatement`, in
`CuspidalPairPartialGammaReduction` and in
`RankinSelberg/PartialEulerProductConvergence`, which do not use the statement.

Complete drafts. The main theorem has exactly the target type of the task (for
Task 6822, of the first of its two targets).

| Task | Draft | Main theorem and helper modules |
| --- | --- | --- |
| Task 6998, `2dd46728-358f-4428-b1ee-387f98752a75` | rev 1, `504b58d0` | `Langlands.Global.cuspidalSplitCentreUnitaryCentralCharacter : CuspidalSplitCentreUnitaryCentralCharacterStatement.{u}`, module `Langlands.Global.Factors.CuspidalSplitCentreUnitaryProof`; helper `Langlands.Global.HeckeCharacterPositiveRealUnitary` (`HeckeCharacter.isUnitary_of_positiveRealIdeles`). Check `b4d6c939` |
| Task 6999, `ae8500ea-b349-43af-a409-c33bbccb5317` | rev 1, `5178d138` | `Langlands.Automorphic.archimedeanStandardAdmissible : ArchimedeanStandardAdmissibleStatement`, module `Langlands.Automorphic.ArchimedeanStandardAdmissibleProof`. The real conjunct is Worker 5220's published `realStandardAdmissible` (previous section). The complex conjunct `Langlands.Archimedean.complexStandardAdmissible` is declared in the same module. It applies `PrincipalSeries.isAdmissibleGKModule_principalSeriesRep` of the helper `Langlands.Representation.Archimedean.PrincipalSeriesAdmissible`, which proves admissibility of the principal series by the same route, for `U(n)`. Check `18a2343f` |
| Task 6818, `7825d219-2a04-4194-9e19-95b05a84c4dc` | rev 1, `8c813a67` | The four targets `realPairLFactorRightHalfPlaneRegularity`, `complexPairLFactorRightHalfPlaneRegularity`, `realUnitaryGenericPairRegularityReduction`, `complexUnitaryGenericPairRegularityReduction` (namespace `Langlands.Archimedean`), one module each under `Langlands/Representation/Archimedean/`, with the helper `PairBlockExponent`. Check `99ee7241` (all four modules) |
| Task 7000, `f273c02c-55ab-425f-b5d0-c51b0ea23a34` | rev 2, `d8656841` | `Langlands.Automorphic.cuspidalArchimedeanStandardUnitarizable` (module `CuspidalArchimedeanComponentUnitaryProof`) and `cuspidalArchimedeanPairRegularityReduction` (module `CuspidalArchimedeanPairRegularityReductionProof`). Check `c3577214` |
| Task 7038, `77a8a491-bc89-4cd8-ad39-99a4c66876f9` | rev 1, `23a8f79c` | `Langlands.Global.cuspidalSupportDataReduction : CuspidalSupportDataReductionStatement.{u}`, module `Langlands.Global.Factors.CuspidalSupportDataReductionProof`. Check `a6992108` |
| Task 6815, `3e10ac73-00ae-4f30-a604-a09968ca2697` | rev 2, `7c4736e8` | `Langlands.Automorphic.localComponentExistence : LocalComponentExistenceStatement.{u}`, module `Langlands.Automorphic.LocalComponentExistenceProof`. The finite places are handled in `LocalComponentFinitePlace` (with the helper `Langlands.Representation.Smooth.JointIsotypicComponent`), the real and complex places in `OperatorSubquotientPlaceComponent` and `OperatorSubquotientPlaceComponentComplex`. The last two port the Library's place-component results for cuspidal realizations to operator subquotients. Check `3c9f926b` |
| Task 6822, `a8e36011-2be8-46cc-a440-0da01109d6e6` (JS I Theorem (5.3) from Lemma (5.2); target 1 of the task) | rev 1, `afd2ba56` | `Langlands.Global.cuspidalPairAbsoluteConvergenceReduction : CuspidalPairAbsoluteConvergenceReductionStatement.{u, uQ}`, module `Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceProof`. The draft adds two helper modules. `Langlands.Analysis.LandauDirichlet` proves Landau's theorem for general Dirichlet series with nonnegative coefficients (Hardy–Riesz 1915, Theorem 10, p.10, registered as `hardy-riesz-1915-dirichlet-series`), also in the exponential form used by JS I, p.556. `Langlands.Representation.Unramified.UnitarySpectrumConjugation` proves that a unitarizable spherical representation with spectrum `s` has `conj s = s⁻¹`. The bound `|α| ≤ q_v^(1/2)` comes from the published `norm_unramifiedClass_le_sqrt`. Check `086a1263`. Target 2 of the task needs a proof of `CuspidalSelfPairContinuationStatement` (Task 6821) |
| Task 7174, `fc99d3a8-d98b-4d1b-933c-db958e05059d` (published by Worker 3657 on the operator's instruction, message `37d9a1c6be9f5f6186de2d70b51a3234`; it replaces Task 5768, `4e277fc9-6303-4213-bb44-eaea2babfdc1`, which the operator retired) | rev 1, `3f16f2f6` | `Langlands.ArthurCombinatorics.arthurCombinatoricsStatement : ArthurCombinatoricsStatement.{u}`, module `Langlands.LinearAlgebra.ArthurCombinatoricsProof`, with the six conjuncts as named theorems in five helper modules `ArthurCombinatorics{Alternating,CartanInverse,Sigma,SigmaSupport,LanglandsLemma}`. Check `c476c2ed`. Worker 3657 asked the operator to assign Worker 7 as executor (request `7cd25bd50845535d81557e43c1c75076`) |

Partial drafts. The main theorem proves the target from the named inputs, or
proves part of it. Each input is a published statement without a public
proof, owned by the task named.

| Task | Draft | Main theorem, inputs, and what remains |
| --- | --- | --- |
| Task 5978, `fd17a0f9-9ab1-46d6-a8d9-af3587d0fdcd` (GH Lemma 11.8.1) | rev 2, `5a7092cb` | `Langlands.Global.cuspidalIsobaricPoleOrder_of_inputs`, from `CuspidalPairPoleStatement` (Task 5921), `CuspidalPairBoundaryNonvanishingStatement` (Task 5816) and `CuspidalSplitCentreUnitaryCentralCharacterStatement` (Task 6998, complete draft above). Proved in the draft: the identity theorem on a half-plane, the splitting of the Euler product at `S` with the unramified comparison of L-polynomials, nonpositive orders of all local factors, Shahidi at `s = 1`, order additivity, and the symmetry of the contragredient relation for cuspidal realizations with unitary central characters (`Langlands.Automorphic.CuspidalOperatorRealization.isContragredientOf_symm`, helper module `Langlands.Automorphic.ContragredientSymmetry`, through the Library's unitary criterion `isContragredientOf_of_unitaryForm`). Check `f74ecc08` |
| Task 6388, `0b0b55d3-ba74-4eea-be8c-03c8b57b3cee` (GH Theorem 11.7.2) | rev 1, `b40942a9` | `Langlands.Global.cuspidalStrongMultiplicityOne_of_eulerConstituentRecovery`, from `CuspidalEulerConstituentRecoveryStatement` (Task 6446), with one constituent on each side. The bridge of §5 of the statement Markdown is proved: equal finite local classes at unramified places give equal Satake spectra, by the Library's `Unramified.sphericalSpectrumUniqueness`. Check `39b9a347` |
| Task 6446, `c4f0be57-1a49-4a42-b813-4354e297ab3f` (JS II Theorems 4.2 and 4.4) | rev 1, `f4607cdc` | `Langlands.Automorphic.Unramified.cuspidalSpectralRigidity_of_independence`, from `CuspidalPowerTraceIndependenceStatement` (JS II Theorem 4.2, the first conjunct of the target). Proved: constituent recovery with multiplicities by the multiplicity comparison of the proof of Theorem 4.4, the Euler form, and the comparison of systems attached to one class. Check `bf47aca5` |
| Task 6816, `876084f9-496c-4109-818b-291f765e1077` | rev 1, `ce0760f3` | `Langlands.Automorphic.localComponentEmbedding_of_localComponentExistence`, from `LocalComponentExistenceStatement` (Task 6815) |
| Task 6817, `0e6a285c-e06e-4df1-a4d3-fbebc025050d` | rev 1, `0ead56e4` | `Langlands.Automorphic.localComponentDetermination_forward`, the forward implication of the target, from `LocalComponentExistenceStatement`. The reverse implication (tensor factorization) is open |
| Task 6824, `5c8e59c5-aa00-4b14-9f2a-3762a62c9314` | rev 1, `045fc62a` | `Langlands.Global.cuspidalSupportUniqueness_of_localComponentExistence`, from `IrreducibleSubquotientAdmissibilityStatement` (Task 6611), `LocalComponentExistenceStatement` (Task 6815) and `CuspidalInducingDataRigidityStatement` (Task 6447) |
| Task 6610, `b03daed8-a989-47ce-81db-ef575e1c4449` | rev 1, `14ea8f3d` | `Langlands.Automorphic.generatedFormAdmissibility_of_harishChandraFiniteness`, from `HarishChandraFinitenessStatement` (Task 6609) |
| Task 6447, `c6bba40a-b120-420c-9c51-9eae3198c17e` (GH Theorem 10.7.2) | rev 3, `f6851b40` | `Langlands.Global.cuspidalInducingDataRigidity_of_constituentRecovery`, from `CuspidalEulerConstituentRecoveryStatement` (Task 6446) alone (module `Langlands.Global.Factors.CuspidalInducingDataRigidityReduction`). The local input of revision 2 is now proved in the draft: `unramifiedProductInducedSpectrum : UnramifiedProductInducedSpectrumStatement` (helper module `Langlands.Representation.Unramified.ProductInducedSpectrum`). It says that at a finite place, a spherical subquotient of `i(σ_1, …, σ_k)` with spherical blocks `σ_i` of spectra `s_i` has the concatenated spectrum (the first step of the proof of JS II Theorem 4.4, p.809). Check `7b4b4ffb` |
| Task 6611, `31e7c233-a07b-411e-884f-e919222d7c3f` (Borel–Jacquet §4.6) | rev 1, `0aaee6da` | `Langlands.Automorphic.irreducibleSubquotientAdmissibility_of_generatedFormAdmissibility`, from `GeneratedFormAdmissibilityStatement` (Task 6610), module `Langlands.Automorphic.IrreducibleSubquotientAdmissibilityReduction`. An irreducible operator subquotient is the image of the realization generated by one automorphic form, and joint admissibility passes to quotients. The quotient step uses the Library's compact Maschke lifting lemma and averaging over a compact open subgroup. Check `bbf430f2` |
| Task 6821, `1d8cbc81-142d-47eb-9f4d-8b2b13f0fd52` (JS I Lemma (5.2)) | rev 1, `c42c8d20` | `Langlands.Global.cuspidalSelfPairContinuationReduction : CuspidalPairPoleStatement.{u, uQ} → CuspidalSelfPairContinuationStatement.{u, uQ}`, from `CuspidalPairPoleStatement` (GH Theorem 11.7.1, Task 5921), module `Langlands.Global.Factors.CuspidalSelfPairContinuationReduction`; route B of the task contract. Helper modules `Langlands.Analysis.ContinuousCharacterReal` (continuous unitary characters of `ℝ` are `u ↦ exp(itu)`) and `Langlands.Global.Factors.SplitCentreTwist`. The latter twists by `|det|^(is)` to reach realizations trivial on the split centre, and proves that the conjugate realization realizes the contragredient. The three modules of the Task 6822 draft are included unchanged. Possible zeros of the archimedean denominators are handled by the identity theorem. Check `7efbdfdc` |

Consequences for the L4 targets. With the drafts of Tasks 6388 and 6446,
strong multiplicity one for cuspidal realizations (GH Theorem 11.7.2) depends
only on JS II Theorem 4.2. That theorem rests on the asymptotics of JS II
Theorem 4.1. Those need JS I Theorem 5.3. By the drafts of Tasks 6822 and 6821, that
theorem depends only on GH Theorem 11.7.1 (Task 5921). They also need the pole at `s = 1`
(GH Theorem 11.7.1, Task 5921, with local regularity) and Shahidi's
nonvanishing (Task 5816). With the drafts of Tasks 5978 and 6998, GH
Lemma 11.8.1 depends only on GH Theorem 11.7.1 and Shahidi's theorem. With the
drafts of Tasks 6447 and 6446, GH Theorem 10.7.2 depends only on JS II Theorem
4.2. With the drafts of Tasks 6611 and 6610, the admissibility of irreducible
automorphic subquotients (Borel–Jacquet §4.6) depends only on Harish-Chandra's
finiteness theorem (Task 6609). The draft of Task 6815 proves the existence of
local components at every place, which is the input of the drafts of Tasks
6816, 6817 and 6824. These
dependencies hold only once the drafts are submitted, reviewed and published.

The shared DAG records each draft on the description of the corresponding
proof node (revisions 270–309). Revision 287 adds an edge from
`proof.cuspidal-strong-multiplicity-one` to `proof.automorphic-rigidity`.
Neither track of the program is complete.

## 17 November 2026 published inputs, totally complex forms and updated drafts

Worker 3657 checked this section against Library
`314cfd1a0275806b9ff4281f3d3e51a05e9a6cb5` on 17 November 2026. Where the two
differ, it supersedes the rows of the previous section for Tasks 5978, 6388,
6446, 6447 and 7174. The conventions of that section apply: a shared draft is
an unreviewed TaskHub draft revision, not a candidate, and "check" is Worker
3657's own private `lean_check` record in environment `5c94c648`. Every main
theorem named below uses only `propext`, `Classical.choice` and `Quot.sound`.
Outside statement modules, no Lean file of Library `314cfd1a` names any of the
input or target statements in the table below or `CuspidalPairPoleTCStatement`,
`CuspidalSpectralRigidityTCStatement`, except the two imports of the
module of `CuspidalPairBoundaryNonvanishingStatement` noted in the previous
section.

### Newly public units

- `Langlands.Global.CuspidalFinitePairRegularityStatement` (module
  `Langlands.Global.Factors.CuspidalFinitePairRegularityStatement`; Getz–Hahn
  Theorem 11.5.2, non-Archimedean case, in the normalization of the pole
  statement): Worker 3657's candidate `342973b1-6f90-40c5-83c4-4d72c6abc3c3`,
  independently reviewed, published in Library `314cfd1a`. Proof task:
  Task 7358, `d1aad7bf-655e-4219-9022-9a2bdba3abe8` (`lean.proof@1`, published
  by Worker 3657, no member at inspection on 17 November 2026).
- `Langlands.ArthurCombinatorics.arthurCombinatoricsStatement` (module
  `Langlands.LinearAlgebra.ArthurCombinatoricsProof`): Worker 7 submitted the
  Task 7174 draft with Worker 3657 as coauthor (candidate
  `f0888780-8ab3-4ea1-848b-d9db50e75aef`). It was independently reviewed and is
  published in Library `314cfd1a`; Task 7174 is completed and closed.
- Worker 0 (Task 0) published totally complex forms of Harris-branch inputs,
  each the original proposition with `[NumberField.IsTotallyComplex F]`
  inserted after `[NumberField F]`. Two of them are inputs of this program's
  L4 targets: `Langlands.Global.CuspidalPairPoleTCStatement` (module
  `Langlands.Global.Factors.CuspidalPairPoleTCStatement`, candidate
  `6fa63d07`) and `Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement`
  (module of the same name, candidate `7d11a931`). Revision 2 of Task 5921
  (`786d8bc1-6a9b-4fa0-ae6c-89e17489000c`) and of Task 6446
  (`c4f0be57-1a49-4a42-b813-4354e297ab3f`), by Worker 3657, ask their
  executors also to submit proofs of these as supporting candidates. That
  request is not an acceptance condition.

### Drafts updated since the previous section

| Task | Draft | Main theorems and inputs |
| --- | --- | --- |
| Task 6446 (JS II Theorems 4.1, 4.2 and the numerical step of 4.4) | rev 4, `bb6a21c9`; rev 2 `2ee10df9` and rev 3 `45b0b5ed` before it | `Langlands.Automorphic.Unramified.cuspidalSpectralRigidity_of_published_inputs : CuspidalSpectralRigidityStatement`, from `CuspidalPairPoleStatement` (Task 5921), `CuspidalPairBoundaryNonvanishingStatement` (Task 5816, `c325654f-b8fb-4a43-9caf-c147e4ae95f2`), `Automorphic.CuspidalArchimedeanPairRegularityStatement` (Task 7005, `1a9d552f-6429-45fa-afcd-7f2806c4312f`) and `RankinSelberg.UnitaryGenericLPolynomialNonvanishingStatement` (Task 6387, `9dcb3206-7035-4d1c-9cea-f620e42f9628`). Revision 4 also proves `cuspidalSpectralRigidityTC_of_published_inputs : CuspidalSpectralRigidityTCStatement` from the same inputs with `CuspidalPairPoleTCStatement` in place of `CuspidalPairPoleStatement`. To do so it restates the proofs over one number field (helper module `Langlands.Global.Factors.CuspidalPairPoleFieldwise`). JS I Lemma (5.2) and Theorem (5.3) are derived inside the draft from the pole statement over the field of the conclusion, through the Task 6821 and Task 6822 drafts; JS II Theorem 4.1 is read off the completed L-function of GH Theorem 11.7.1, with Shahidi's theorem on `Re s = 1`. The finite regularity statement is derived from the Task 6387 statement by `Langlands.Global.cuspidalFinitePairRegularity_of_unitaryGeneric`. Check `06f14573` (rev 3: `c1360622`) |
| Task 6388, `0b0b55d3-ba74-4eea-be8c-03c8b57b3cee` (GH Theorem 11.7.2) | rev 4, `acc89d94` | `Langlands.Global.cuspidalStrongMultiplicityOne_of_published_inputs : CuspidalStrongMultiplicityOneStatement`, from the four inputs of the Task 6446 draft (its modules copied), through the revision 1 reduction to `CuspidalEulerConstituentRecoveryStatement`. Check `e2058312` |
| Task 6447, `c6bba40a-b120-420c-9c51-9eae3198c17e` (GH Theorem 10.7.2) | rev 5, `6560a70b` | `Langlands.Global.cuspidalInducingDataRigidity_of_published_inputs : CuspidalInducingDataRigidityStatement`, from the same four inputs, through the revision 3 reduction to `CuspidalEulerConstituentRecoveryStatement`. Check `eb3ad2e5` |
| Task 5978, `fd17a0f9-9ab1-46d6-a8d9-af3587d0fdcd` (GH Lemma 11.8.1) | rev 3, `cc923262` | `Langlands.Global.cuspidalIsobaricPoleOrder_of_published_inputs : CuspidalIsobaricPoleOrderStatement`, from `CuspidalPairPoleStatement` (Task 5921) and `CuspidalPairBoundaryNonvanishingStatement` (Task 5816) only; the input `CuspidalSplitCentreUnitaryCentralCharacterStatement` is discharged by the proof `cuspidalSplitCentreUnitaryCentralCharacter` of the complete Task 6998 draft, copied in. Check `58939234` |
| Task 7358 (finite pair regularity) | rev 1, `d7073f3a` | `Langlands.Global.cuspidalFinitePairRegularity_of_unitaryGeneric : UnitaryGenericLPolynomialNonvanishingStatement.{u, u, u} → CuspidalFinitePairRegularityStatement.{u, uQ}`, via the proved `cuspidalUnitaryLocalGenericity`, `cuspidalUnitaryLocalUnitarity` and `genericLanglandsQuotientLFactor` (JPSS 1983, Proposition (9.4), display (4)). Check `c0d9598d` |

None of Tasks 5978, 6388, 6446, 6447 and 7358 had a member at Worker 3657's
latest inspection (16–17 November 2026).

### Consequences for the L4 targets

Through these drafts, once they are submitted, reviewed and published:

- GH Theorem 11.7.2 (strong multiplicity one), GH Theorem 10.7.2 (rigidity of
  cuspidal inducing data) and the three conjuncts of Jacquet–Shalika rigidity
  depend only on the targets of Tasks 5921, 5816, 7005 and 6387;
- the totally complex form of Jacquet–Shalika rigidity (Harris's input 9)
  depends only on a proof of `CuspidalPairPoleTCStatement` and the targets of
  Tasks 5816, 7005 and 6387;
- GH Lemma 11.8.1 depends only on the targets of Tasks 5921 and 5816.

For these targets, the statements named in the three items are the remaining
analytic inputs. None of them is proved in Library `314cfd1a`. The other open
inputs of the program recorded in earlier sections (for example Harish-Chandra
finiteness, Task 6609, and the truncation block of Task 5536) are unchanged.

The shared DAG records the drafts on the corresponding proof nodes
(revisions 310–349), including `proof.cuspidal-finite-pair-regularity` (Task
7358) and `proof.tc-automorphic-rigidity`. Neither track of the program is
complete.

## 17 November 2026 (later) complete drafts for Getz–Hahn Theorem 11.5.2, p-adic case, and finite pair regularity

Worker 3657 checked this section against Library
`fcb85a7ef43356fec01e6ccf1605f08568c08cb0` on 17 November 2026. The
conventions of the two previous sections apply: a shared draft is an
unreviewed TaskHub draft revision, not a candidate, and "check" is Worker
3657's own private `lean_check` record in environment `5c94c648`. Every theorem
named below uses only `propext`, `Classical.choice` and `Quot.sound`. Outside
statement modules, no Lean file of Library `fcb85a7e` names
`UnitaryGenericLPolynomialNonvanishingStatement`,
`CuspidalFinitePairRegularityStatement`, `UnitaryEqualRankConvergenceStatement`
or the statements of Tasks 5921 and 7005, and the only files naming the statement
of Task 5816 are the two imports noted in the 15 November section.

### New complete drafts

| Task | Draft | Main theorem |
| --- | --- | --- |
| Task 6387, `9dcb3206-7035-4d1c-9cea-f620e42f9628` (GH Theorem 11.5.2, p-adic case) | rev 1, `7598cd1e` | `Langlands.RankinSelberg.UnitaryGeneric.unitaryGenericLPolynomialNonvanishing : UnitaryGenericLPolynomialNonvanishingStatement.{uF, uV, uW}`, with no hypotheses. Seven modules under `Langlands/Representation/RankinSelberg/`: `UnitaryWhittakerTorusSum` (Jacquet–Shalika I, (1.3.1), in torus form, from the published `padicCellBound`), `UnitaryWhittakerRestriction`, `UnitaryWeightedWhittakerSquare` (exponents `a ≥ 1/2`), `UnitaryEqualRankAnalytic` and `UnitaryZeroRowAnalytic` (convergence on `Re s ≥ 1`, holomorphy on `Re s > 1`), `BoundaryRationalRegularity` (regularity of rational continuations on `Re s = 1` from boundedness on a strip) and the assembly `UnitaryGenericLPolynomialNonvanishingProof`. The draft also proves the published `UnitaryEqualRankConvergenceStatement` (Jacquet–Shalika I, Proposition (1.5)(i)) as `unitaryEqualRankConvergence`. Checks `ffc7fc36`, `2bf88205`, `dddc6727` |
| Task 7358, `d1aad7bf-655e-4219-9022-9a2bdba3abe8` (finite pair regularity) | rev 2, `e61d62f1` | `Langlands.Global.cuspidalFinitePairRegularity : CuspidalFinitePairRegularityStatement.{u, uQ}`, with no hypotheses: the revision 1 reduction applied to the Task 6387 draft proof, whose modules are copied. Check `4ef06a63` |

Neither task has a member. Worker 3657 cannot submit these proofs while
executing Task 3657 and asked the operator to assign executors (request
`7a6a0449d7d659e894ab371e30e599f0`, pending), also for the earlier complete
drafts of the 15 November section.

### Updated partial drafts

| Task | Draft | Main theorem and remaining inputs |
| --- | --- | --- |
| Task 6446 | rev 5, `e9650f8d` | `cuspidalSpectralRigidity_of_analytic_inputs` and `cuspidalSpectralRigidityTC_of_analytic_inputs`: `CuspidalSpectralRigidityStatement` from the targets of Tasks 5921, 5816 and 7005, and its totally complex form with `CuspidalPairPoleTCStatement` in place of the target of Task 5921. Check `9364be54` |
| Task 6388 | rev 5, `e010a7c7` | `cuspidalStrongMultiplicityOne_of_analytic_inputs`, from the targets of Tasks 5921, 5816 and 7005. Check `91118822` |
| Task 6447 | rev 6, `07667acd` | `cuspidalInducingDataRigidity_of_analytic_inputs`, from the targets of Tasks 5921, 5816 and 7005. Check `f20135b5` |

Each of these drafts copies the seven Task 6387 modules.

### Consequences

Once the drafts are submitted, reviewed and published, the p-adic regularity
input leaves the list of the previous section. Jacquet–Shalika rigidity, strong
multiplicity one (GH Theorem 11.7.2) and the rigidity of cuspidal inducing data
(GH Theorem 10.7.2) then depend only on the targets of Tasks 5921, 5816 and
7005. The totally complex form of Jacquet–Shalika rigidity (Harris's input 9)
depends only on a proof of `CuspidalPairPoleTCStatement` and the targets of
Tasks 5816 and 7005. None of these three remaining statements is proved in
Library `fcb85a7e`.

The shared DAG records these drafts at revision 372. Neither track of the
program is complete.

## 17 November 2026 (evening) publications, the reverse local-component theorem and refreshed drafts

Worker 3657 checked this section against Library
`ab9053b1751d6b6557d044c38c04e4c8a67dfffc` on 17 November 2026. The
conventions of the previous sections apply: a shared draft is an unreviewed
TaskHub draft revision, not a candidate, and "check" is Worker 3657's own
private `lean_check` record in environment `5c94c648`. Every theorem named
below uses only `propext`, `Classical.choice` and `Quot.sound`.

### Proofs published since the previous section

Each of these tasks was published by Worker 3657 under this program. Its
executor staged Worker 3657's complete draft with Worker 3657 as coauthor,
and the candidate was independently reviewed and is in Library `ab9053b1`.
All these tasks except Task 6822 are completed; Task 6822 waits for its second
target.

| Task | Candidate(s) | Executor |
| --- | --- | --- |
| Task 6387, `9dcb3206-7035-4d1c-9cea-f620e42f9628` (GH Theorem 11.5.2, p-adic case) | `144249d7` | Worker 828 |
| Task 6998, `2dd46728-358f-4428-b1ee-387f98752a75` | `e87a1374` | Worker 830 |
| Task 6999, `ae8500ea-b349-43af-a409-c33bbccb5317` | `adf41064` | Worker 378 |
| Task 7000, `f273c02c-55ab-425f-b5d0-c51b0ea23a34` (two targets) | `0d0bbf6e`, `b44d9db1` | Worker 832 |
| Task 7038, `77a8a491-bc89-4cd8-ad39-99a4c66876f9` (`CuspidalSupportDataReductionStatement`) | `3992f269` | Worker 573 |
| Task 6815, `3e10ac73-00ae-4f30-a604-a09968ca2697` (`LocalComponentExistenceStatement`) | `86aa9114` | Worker 833 |
| Task 6818, `7825d219-2a04-4194-9e19-95b05a84c4dc` (four targets) | `09de17d3`, `5cbfcc13`, `9776299d`, `c1f2082e` | Worker 831 |
| Task 6822, `a8e36011-2be8-46cc-a440-0da01109d6e6` (target 1, JS I Theorem (5.3) from Lemma (5.2)) | `37f9ec80` | Worker 834 |

Staged but not yet published at this check:

- Task 7358 (`d1aad7bf-655e-4219-9022-9a2bdba3abe8`, finite pair
  regularity): candidate `764465be-4c04-4509-b0e8-5b0e2ab97e9c` by Worker 829,
  with Worker 3657 as coauthor (module
  `Langlands.Global.Factors.CuspidalFinitePairRegularityProof`). Machine
  validation accepted; peer review pending.
- The four helper modules of the Task 7003 draft (real-place nonvanishing of
  standard modules): candidate `72a4ffa0-e91a-474c-b2da-ccacba8bccd0`, staged
  by Worker 771 under Task 7400 with Worker 3657 as coauthor. Review accepted,
  not yet integrated in Library `ab9053b1`.

### New complete drafts

| Task | Draft | Main theorem |
| --- | --- | --- |
| Task 6817, `0e6a285c-e06e-4df1-a4d3-fbebc025050d` (GH Theorem 6.3.7 and the uniqueness of the factors; Flath Theorem 3) | rev 2, `3386f6fc` | `Langlands.Automorphic.localComponentDetermination : LocalComponentDeterminationStatement.{u}`, with no hypotheses, from the published `localComponentExistence`. Seven modules: `OpenSubgroupInduction` (open subgroups of `GL_n(𝔸_f)`, induction over local factors), `CommutingFamilyUniqueness` (an abstract uniqueness theorem for commuting, jointly irreducible families of isotypic actions with scalar self-intertwiners, almost-everywhere spherical lines and smooth vectors), `FreeMonoidGenerators` (the place actions read as free-monoid representations; common isotypic types), `OperatorSubquotientPlaceGeneration` (the place actions generate the operator algebra), and the forward, reverse and final modules `LocalComponentDetermination{Forward,Reverse,Proof}`. The reverse implication does not build the restricted tensor factorization; it uses the same inputs (isotypy at each place, Schur, one-dimensional spherical lines, smoothness) in the abstract theorem. Check `dbe84f71` |
| Task 6816, `876084f9-496c-4109-818b-291f765e1077` (`LocalComponentEmbeddingStatement`) | rev 4, `809a6c3a` | `Langlands.Automorphic.localComponentEmbedding`, unchanged; revision 4 imports the published Task 6815 modules instead of copying them. Check `f6d6a64d` |

Task 7003 (`d785ecd7-e7cc-4174-9da9-68b37467f224`) keeps its complete draft
revision 2 (`cce64d95`). Tasks 6816, 6817 and 7003 had no member at this
check; Worker 3657 asked the operator to assign executors.

### Refreshed partial drafts

| Task | Draft | Change |
| --- | --- | --- |
| Task 6446 | rev 6, `58fe338e` | imports the published Task 6387, 6822 and 6998 modules instead of copies; mathematics unchanged. Check `a0ff5d68` |
| Task 6388 | rev 6, `9f348f49` | the same. Check `bde54f5d` |
| Task 6447 | rev 7, `53ffbcfd` | the same. Check `42b0094c` |

These three drafts still contain modified versions of two published modules,
`Langlands.Automorphic.ContragredientUniqueness` and
`Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceProof` (fieldwise
forms added). Before any of them is submitted, the additions must move to new
modules; their Markdown says so. Their remaining inputs are unchanged: the
targets of Tasks 5921 (or `CuspidalPairPoleTCStatement` for the totally
complex form), 5816 and 7005.

### Consequences

- The local-component block of statement module
  `Langlands.Automorphic.OperatorSubquotientLocalComponentStatement` is now
  covered: existence is published, and complete drafts prove the embedding and
  determination statements. Once Task 6817 is submitted, reviewed and
  published, step 1 of the expected route of the isobaric strong multiplicity
  one task (Task 6554, `377cdd2a-1281-43b5-bd23-92836e2f056f`) has all its
  local-component inputs.
- The status of the L4 analytic inputs is as in the previous section: the
  rigidity theorems and GH Theorem 11.7.2 depend only on the targets of
  Tasks 5921, 5816 and 7005, none of which is proved in Library `ab9053b1`.

The shared DAG records the Task 6817 draft at revision 440. Neither track of
the program is complete.

## 17 November 2026 (night) Flath's Example 2, refreshed drafts and the archimedean exponent bounds

Worker 3657 checked this section against Library
`70eba6bb71c0dfc732a95146e6f12219c3cc76ae` on 17 November 2026. The
conventions of the previous sections apply. Every theorem named below uses only
`propext`, `Classical.choice` and `Quot.sound`.

### Newly public

- The four helper modules of the Task 7003 draft (`InversePowerFourier`,
  `RealGramFunction`, `RealStandardBlockPolynomial`,
  `RealStandardNontrivialProof`; real-place nonvanishing of standard modules):
  candidate `72a4ffa0-e91a-474c-b2da-ccacba8bccd0` (Worker 771, Task 7400, with
  Worker 3657 as coauthor), now in Library `70eba6bb`.

### New proof tasks with complete drafts (Flath 1979, §2, Example 2)

`Langlands.FlathRestrictedTensorStatement`
(`Langlands/Representation/Smooth/Factorization/RestrictedTensorStatement.lean`)
is the conjunction of four clauses; only the factor-uniqueness clause was proved
in the Library (`restrictedTensorFactorUniqueness`). Worker 3657 published one
`lean.proof@1` task per remaining clause and for the assembly, each with a
complete shared draft. TaskHub searches found no earlier task for any of them.

| Task | Target | Draft | Main theorem and route |
| --- | --- | --- | --- |
| Task 7587, `c34533a5-e6ae-41c5-b91e-f54fe1406d2d` | `RestrictedTensorReferenceIndependenceStatement` | rev 1, `abd55898` | `restrictedTensorReferenceIndependence`: rescaling the reference vectors on the fixed lines, with the Library's `RestrictedTensor.congr` and `map_intertwines`. Check `2d5c744d` |
| Task 7588, `07bc4cad-b1bb-4697-9621-72d53c6f2a68` | `RestrictedTensorIrreducibilityStatement` | rev 2, `ca1a959d` | `restrictedTensorIrreducibility`: local ⇒ global through finite stages and the Library's `FiniteTensor.isIrreducible_external` with admissible Schur; global ⇒ local through the kernel of the map to the tensor with `V j` replaced by `V j ⧸ W`. Helper module `RestrictedTensor.StageAction`. Check `42831b37` |
| Task 7602, `2d9e8c06-2e8e-4a00-84bd-3af86ce4608e` | `RestrictedTensorAdmissibilityStatement` | rev 1, `7238da68` | `restrictedTensorAdmissibility`: an open subgroup contains a product of local open subgroups (trivial up to `H i` off a finite set), and its fixed vectors lie in a finite stage (`FiniteTensor.fixedVectors_external_le`). Same helper module. Check `8ce744a0` |
| Task 7606, `5463cefc-0424-4c7b-ae7a-4e99b99b7027` | `FlathRestrictedTensorStatement` | rev 1, `8ed0f0f4` | `flathRestrictedTensor`: the conjunction; it compiles together with the three drafts above (check `5bcf871c`) and is staged after they are published |

None of these tasks had a member at this check.

### Refreshed drafts

| Task | Draft | Change |
| --- | --- | --- |
| Task 6446 | rev 7, `a05a348d` | The draft no longer contains modified copies of published modules: the fieldwise additions moved to the new modules `Langlands.Automorphic.RealizationEquivalenceTransport` and `Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceFieldwise`, over the published `ContragredientUniqueness` and `CuspidalPairAbsoluteConvergenceProof`. This resolves the caveat recorded in the previous section. Check `33ffce66` |
| Task 6388 | rev 7, `8c22bc57` | The same. Check `fdc456e2` |
| Task 6447 | rev 8, `455eb049` | The same. Check `10e282d1` |
| Task 6824, `5c8e59c5-aa00-4b14-9f2a-3762a62c9314` | rev 2, `2d85a0a0` | Adds `cuspidalSupportUniqueness_of_admissibility_rigidity`, discharging the local-component hypothesis with the published `localComponentExistence`; the remaining inputs are the targets of Tasks 6611 and 6447. Check `77da5e27` |
| Task 5978 | rev 4, `092719bd` | Imports the published Task 6998 modules instead of copies. Check `41248fd7` |
| Task 7003 | rev 3, `77966f67` | One module, importing the four published helpers; still complete. Check `4ab0d514` |

### The archimedean exponent bounds

In `Langlands/Representation/Archimedean/UnitaryGenericPairRegularityStatement.lean`
the right half-plane regularity of real and complex pair `L`-factors and both
reductions are proved in the Library. The only missing inputs of the
archimedean case of Getz–Hahn Theorem 11.5.2 are
`RealUnitaryGenericExponentBoundStatement` and
`ComplexUnitaryGenericExponentBoundStatement` (`|Re t| < 1/2` for the blocks of
a standard parameter of a generic unitarizable module). Worker 3657 published
Task 7607 (`5d2d0305-72dc-470c-8489-ab38acef4fba`) for them, with the route of
the statement Markdown (Badulescu–Renard 2010, Theorems 8.1 and 8.2); no draft
is shared. The Library's `cuspidalArchimedeanPairRegularityReduction` derives
the archimedean pair regularity of Task 7005 from these two bounds (through the
proved reductions), the published `archimedeanStandardAdmissible` and
`cuspidalArchimedeanStandardUnitarizable`, the genericity statement of Task 7003
(complete draft) and the irreducibility of archimedean standard modules
(Task 7004, open).

The status of the other L4 inputs (Tasks 5921 and 5816) is unchanged at this
snapshot. The shared DAG records the Flath drafts at revision 450. Neither
track of the program is complete.

## Publication update, 20 November 2026

The following results were verified in the current Library at `7ae0d83b7cb2ad9aaca52ada487b3a5d3314323a`.
The table records the integration commit of each candidate, not the date of
machine validation or independent review alone.

| Track and owner | Public declaration(s) | Candidate and integration commit | Scope |
| --- | --- | --- | --- |
| L4, Task 7004 (`c77dc5a4-25c6-4498-bc30-ecfbcf470106`, done) | `Langlands.Automorphic.cuspidalArchimedeanStandardIrreducible`, `Langlands.Automorphic.CuspidalArchimedeanComponentIrreducibleProof` | `7c7a323a-a027-4428-9456-7f4d5f99dad4`, `5f5d3a914cd43b9dc1cd32c07887a973f561df96` | Exact proof for both real and complex place parameters in Getz–Hahn §11.4, (11.14)–(11.17). It uses isotypy and a compact multiplicity-one witness, not the open generic exponent bounds. |
| L4, Task 6821 (`1d8cbc81-142d-47eb-9f4d-8b2b13f0fd52`) | `Langlands.Global.cuspidalSelfPairContinuation`, `Langlands.Global.Factors.CuspidalSelfPairContinuationProof` | `252cfd3f-ba30-42ae-8074-0499eae137eb`, `95d37e11bd46972d484c6fc9e6b864ff7625cf9e` | Exact proof of the partial self-pair continuation target from Jacquet–Shalika I, Lemma (5.2), pp.554–555. For the specified contragredient and unitary central character it also supplies absolute product convergence throughout `Re s > 1`. The positive global integral, bilateral Landau theorem and nonnegative logarithmic series replace the proposed reduction through Task 5921. |
| L4, Task 3657 | `Langlands.Global.CuspidalPairPoleReductionStatement`, with new premise definitions for slab pairing, semi-local ratios and strip bounds | `517128c6-87c0-46fb-9a59-aad111b56771`, `95d37e11bd46972d484c6fc9e6b864ff7625cf9e` | Proposition definitions, not an exact proof. For Getz–Hahn 11.7.1 (Cogdell 2004 §4, pp.219–222) the four premises are `CuspidalArchimedeanParameterExistenceStatement`, `RankinSelbergGlobal.CuspidalSlabPairingStatement`, `CuspidalPairSemilocalRatioStatement` and `CuspidalPairVerticalStripStatement`. The archimedean existence premise for both real and complex places is open under Task 5720 (`a2cfc970-9e20-4d56-b053-8f91a2e0b5cc`); `cuspidalArchimedeanParameterExistenceTC` covers totally complex fields only. The implication is distinct from the direct Cogdell route of Task 5921. |
| L3, Task 5696 (`5453d037-1d90-4f14-a068-e04f492be43e`) | `Langlands.Global.standardParabolicSpectrumFiniteness`, `Langlands.Global.AdelicStandardParabolicFiniteness` | `1c8d476a-4bc9-48b0-a618-8200c5baec93`, `95d37e11bd46972d484c6fc9e6b864ff7625cf9e` | The finiteness part of Getz–Hahn 10.5.1, conditional on equality of spectra for associate presented standard parabolics. Uses rational parabolic classification and Levi conjugacy. |
| L3, Task 5696 | `Langlands.Global.spectralDecomposition_of_reduction`, `Langlands.Global.AdelicSpectralDecompositionReduction` | `6a3e829a-0f88-44a5-b2f0-79722dcd9c9f`, `95d37e11bd46972d484c6fc9e6b864ff7625cf9e` | Proves Getz–Hahn 10.5.1 assuming `RelativeWavePacketOrthogonalityStatement`, `RelativeWavePacketAssociationStatement`, `RelativeWavePacketCompletenessStatement` and `GroupParabolicSpectrumStatement`. None of the four inputs is proved by this publication. |

For Task 7005, Task 7004 is now a proved input, and Task 7003
(`d785ecd7-e7cc-4174-9da9-68b37467f224`) has also published the exact proof
`Langlands.Automorphic.cuspidalArchimedeanStandardGeneric`
(`7ce500b4-e0af-4d94-b7f0-f4b37ffb9f1d`, commit
`95d37e11bd46972d484c6fc9e6b864ff7625cf9e`). This supersedes the draft status
above. It proves genericity for supplied real and complex place parameters,
not their existence. Use the existing exponent-bound owners (Task 6819,
real bound target, and Task 6820, complex bound); Task 7607 proposes the same
targets and is not an additional proof dependency. The full pole/strip target
is still owned by Task 5921, and the global boundary nonvanishing target by
Task 5816. Neither the conditional pole statements nor the self-pair proof
replaces them.

For Task 5696, the orthogonality and completeness inputs still need the
passage from the full rational quotient of Lapid Proposition 2 and Delorme
Theorem 7.9 to the split-centre quotient of Getz–Hahn §10.5, pp.281–282. The
paired reduction Markdown explains the required central twist and product
wave-packet factorization; its proof does not implement them. Pullback of a
centre-invariant function on `[G]` alone does not give an `L²` function on the
full quotient when the split-centre factor has infinite Haar measure.
The shared DAG records these publication statuses at revision 566. Neither
program track is complete.
