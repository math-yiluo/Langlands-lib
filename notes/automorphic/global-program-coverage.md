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
The receipt section separately identifies checked public results.

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
