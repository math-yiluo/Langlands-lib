# Harris 1998 Proposition 4.8: reduction and proof status

The statements described below are in the Library; the proof status of
each, as found in the Library, is given in the tables.

The original target is
`Langlands.Global.Harris.Proposition48Statement`, in
`Langlands.Global.Arithmetic.HarrisProposition48Statement`. Its statement
and `IsProposition48Datum` stay unchanged. The new derived reduction is
`Langlands.Global.Harris.Proposition48ReductionStatement`, in
`Langlands.Global.Arithmetic.HarrisProposition48ReductionStatement`.
It has fourteen explicit conjuncts and conclusion
`Proposition48Statement.{uF,0,0,0,uV}` for arbitrary independent `uF,uV`,
as required by both Henniart globalization consumers. A statement is not
a proof of its hypotheses.

The final assembly of the original target must import the reduction proof
and all input proofs; retaining those inputs as theorem hypotheses does not
prove Proposition 4.8. The Library proves the reduction
(`proposition48Reduction`) and has the conditional `proposition48_of_hasSolution`;
it does not prove `Proposition48Statement`.

## Fourteen explicit inputs

The table follows the Lean conjunction order. Names beginning
`Proposition48` are in `Langlands.Global.Harris`; the comparison and
Theorem 1.2 are in `Langlands.GaloisRepresentation`; the other names are
in `Langlands.Automorphic.Unramified`. The table gives the proof status of
each input in the Library.

| Input | Proof status | Scope |
| --- | --- | --- |
| `Proposition48AuxiliaryRankOneStatement` | proved: `proposition48AuxiliaryRankOne` | Genuine Hecke-character realization on GL(1), with all four output properties. |
| `Proposition48AuxiliaryParityNormalizationStatement` | no theorem; it follows from proved results: `proposition48AuxiliaryParityNormalizationReduction` with `normTwistInfinity`, `cmNormConjugation`, `proposition48PlaceNormTwist` and `generalPositionAmbientTwist` | Conjugate-inverse CM base character, actual norm correction and preserved one-place validity. |
| `Proposition48AuxiliaryParityUntwistStatement` | no theorem; it follows from proved results: `proposition48AuxiliaryParityUntwistReduction` with `heckeDeterminantTwistWeakInduction`, `heckeDeterminantTwistConjugateSelfDual` and `heckeDeterminantTwistSupercuspidal` | Actual raw/corrected realizations related by multiplication by `ν(det g)`. |
| `Proposition48MackeyStepStatement` | proved: `proposition48MackeyStep` | One compatible prime cyclic field and all actual raw children, exact rank and smaller closure degree. |
| `Proposition48PrimeBranchStatement` | open | Prime orbit, actual transfers and spectral attachments, local distinctness, final assembly. |
| `Proposition48SingletonBranchStatement` | open | Actual local descent, finite-character correction and extension selection. |
| `Harris1998Theorem12CuspidalStatement` | open | Existing cuspidal target; its proof needs a geometric decomposition. |
| `HarrisSupercuspidalLocalComparisonStatement` | open (the Library has the conditional `harrisSupercuspidalLocalComparison_of_canonical`, from `Harris1999Theorem59iiParameterStatement` and `HarrisSupercuspidalRestrictionIrreducibleStatement`) | General cohomological coefficients; pairwise forward local comparison at split supercuspidal places. |
| `CuspidalSpectralRigidityStatement` | open (the Library has the conditional `cuspidalSpectralRigidityLandauReduction`, from `CuspidalPairPoleStatement` with the proved `cuspidalPairAbsoluteConvergence`) | Existing deep Euler constituent rigidity statement; not duplicated. |
| `Proposition48IsobaricInvarianceStatement` | proved: `proposition48IsobaricInvariance` | Conditional multiplicity-preserving Galois invariance from supplied Euler presentations and rigidity. |
| `CyclicRegularInductionStatement` | open (the Library has the conditional `cyclicRegularInductionNormReduction`, from `CyclicRegularInductionExistenceStatement` and `CuspidalEulerConstituentRecoveryStatement`) | Existing Arthur–Clozel target. |
| `CyclicRegularOrbitLiftStatement` | open (the Library has the conditional `cyclicRegularOrbitLiftReduction`, from `CyclicRegularInductionExistenceStatement`, `WeakInductionOrbitBaseChangeStatement` and `CyclicWeakBaseChangePairMultiplicityStatement`) | Actual isobaric lift of the full regular orbit, with all target hypotheses retained. |
| `CyclicStableDescentStatement` | open | Actual cuspidal descents and finite-twist classification. |
| `CyclicWeakInductionSupercuspidalStatement` | open (the Library has the conditional `cyclicWeakInductionSupercuspidal_of_matching_at_completion`) | Henniart–Herb consequence, including actual local/global induction matching. |

Theorem 1.2 is in
`Langlands.Galois.Harris1998ExistenceStatement`; comparison in
`Langlands.Galois.HarrisSupercuspidalLocalComparisonStatement`;
rigidity in
`Langlands.Automorphic.Unramified.CuspidalSpectralRigidityStatement`;
regular induction and stable descent in
`Langlands.Automorphic.Unramified.CyclicTransferStatement`; orbit lift
in `Langlands.Automorphic.Unramified.IsobaricCyclicTransferStatement`;
the Henniart–Herb consequence in
`Langlands.Automorphic.Unramified.CyclicWeakInductionSupercuspidalStatement`.
The new Proposition48 statements have matching `HarrisProposition48…`
module stems in `Langlands.Global.Arithmetic`; the first three share
`HarrisProposition48AuxiliaryInputStatement`.

The companion `Proposition48RankOneStatement` is proved
(`proposition48RankOne`). The full two-place parity statements
`Proposition48ParityNormalizationStatement`,
`Proposition48ParityUntwistStatement`, their conjunction
`Proposition48ParityTransportStatement` and the direct conjunction assembly
`Proposition48AuxiliaryPreparationStatement`, which uses the separate
rank-one proof, are not theorems of the Library but follow from proved results; see
[parity correction and determinant untwisting](proposition-48-parity-transport.md).
The two-place companions do not imply the weaker-hypothesis
one-place inputs: an arbitrary child need not supply a second,
independently compatible completion identification.

## Totally complex companions

The Library also states
`Langlands.Global.Harris.Proposition48ReductionTCStatement` and its
three companion statements in
`Langlands.Global.Arithmetic.HarrisProposition48ReductionTCStatement`.
They retain the original conclusion and universes. Inputs 1–4, 7 and 8
in the table are unchanged; inputs 5, 6 and 9–14 use their totally
complex forms. Their proof status:

| Companion | Proof |
| --- | --- |
| `Proposition48ReductionTCStatement` | proved: `proposition48ReductionTC` |
| `Proposition48PrimeBranchTCStatement` | open |
| `Proposition48SingletonBranchTCStatement` | open |
| `Proposition48IsobaricInvarianceTCStatement` | proved: `proposition48IsobaricInvarianceTC` |
| `CuspidalSpectralRigidityTCStatement` | open (conditional `cuspidalSpectralRigidityTC_of_normalizedContinuation`) |
| `CyclicRegularInductionTCStatement`, `CyclicRegularOrbitLiftTCStatement`, `CyclicStableDescentTCStatement` | open |
| `CyclicWeakInductionSupercuspidalTCStatement` | open (conditional `cyclicWeakInductionSupercuspidalTC_of_gammaOrder`) |

The first four names have namespace `Langlands.Global.Harris`; the last
five have namespace `Langlands.Automorphic.Unramified`. Rigidity is in
`Langlands.Automorphic.Unramified.CuspidalSpectralRigidityTCStatement`;
the four cyclic names are in
`Langlands.Automorphic.Unramified.CyclicTransferInputsTCStatement`.
These are additional published statements, with separate proof
obligations. An original conditional branch proof alone does not prove
its companion, whose foundational hypotheses are weaker. No implication
between the original reduction and its companion is assumed.

The reduction passes the foundational inputs to the branches. Within
the branches the fields are CM or finite extensions of CM fields.
Mathlib's `NumberField.IsCMField.isTotallyComplex` and
`NumberField.isTotallyComplex_of_algebra` supply the totally complex
instances. Thus this restriction presents no known field-instance
obstruction; constructing the actual branch witnesses is the remaining
work of the branches.

## Source-to-declaration route

The source is registered `harris-1998-local-langlands`, M. Harris,
Invent. Math. 134 (1998), 177–210. Printed pages 201–203 are one-based
PDF pages 25–27. The companion TeX is `math_9611226v1.tex`.
The formulations below are derived interfaces where indicated, rather
than claims that Harris printed these Lean-shaped statements.

1. **Arithmetic setup and induction.** Proposition 4.8 is TeX
1554–1561. Its proof chooses fields `E_i` from the local general-position
tower, identifies Mackey constituents `I(a,i,ξ)`, and uses smaller
normal-closure degree, TeX 1574–1614. The internal definitions are in
`HarrisProposition48InductionData`, `HarrisProposition48MackeyData`,
`HarrisProposition48ParityData` and `HarrisProposition48AuxiliaryData`.
`Proposition48MackeyStepStatement` chooses one compatible prime cyclic
`D/E`, with every representative-indexed raw child for `D·a(E')/D`.
Its three inherited conditions express (i) relative regularity,
(ii) conjugate inversion, and (iii) general position at the auxiliary
place. It also records the raw inherited infinity parity, exact
Mackey rank `[D·a(E'):D]`, one-or-prime index cardinality and strict
decrease of `[L:E]`. The choice is joint; inheritance for every
intermediate field is not assumed.
2. **Rank one and changing parity.** The rank-one sentence is printed
p.202, TeX 1588–1590. The auxiliary rank-one input realizes the actual
Hecke character on GL(1). The internal induction first corrects the
child's inherited parity to its own rank parity, applies induction on
the same fields, then untwists on actual realizations. Raw `S` need
not be regular algebraic; corrected `T` must be. Full validity of the
original datum implies auxiliary validity, and `HasSolution` is exactly
the original four-part output, so this one-place organization does not
alter the target.
3. **Global Galois existence.** Theorem 1.2, printed pp.185–186, is
reused in its published cuspidal form. Its output is a finite sum of
pure compatible families with existential coefficient field/embedding,
total rank and weak unramified association. It does not already give
a single common-weight family or arbitrary ramified comparison.
Its proof needs a geometric decomposition that keeps the
Clozel/Kottwitz/Taylor and parity obligations. The compatible-family
framework and the Harris–Berkovich cohomological framework keep their
existing scope.
4. **General coefficients.** The Remark, printed p.202, TeX 1616–1628,
explicitly needs arbitrary cohomological infinity types. The existing
`Harris1999Theorem59iStatement` concerns part (i) and does not supply
this local comparison. The derived pairwise comparison is sourced
instead to Harris 1999 Theorem 5.9(ii), printed pp.314–315, equations
(5.4)–(5.6) and Lemma 5.8 on pp.313–314, together with Harris 1998
Theorem 1.7, pp.189–190. The registered 1999 source is
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`; it is
not identified with the differently titled historical 1998 manuscript.
The comparison retains regular algebraicity, conjugate self-duality,
split place, supercuspidal local factors, rank greater than one and
common pure weight, coefficient field and embedding. Its proof must
compare supplied families to cohomological families and account for
weight scaling and semisimplification. Rank one uses class field theory.
5. **Isobaric Galois invariance.** Printed p.202, TeX 1630–1644,
especially 1641–1644, uses strong multiplicity one. The supplied
Euler presentations of an actual isobaric multiset and its Galois
conjugate feed the conditional invariance statement. The existing
`CuspidalSpectralRigidityStatement` is the suitable input: it recovers
constituents with multiplicities across positive ranks. A direct
cuspidal-only SMO statement does not express this entire step.
Constructing the presentations and proving their Euler equality from
monomial restriction belong to the branch proofs.
6. **Prime orbit.** Printed p.203, TeX 1646–1664, applies
Arthur–Clozel III.6.4 to the full orbit. The existing regular-induction
and isobaric orbit-lift statements are explicit premises of the prime
branch. The registered source is `arthur-clozel-1989-base-change`,
Chapter III, especially Theorem 6.2 and Lemmas 6.3–6.4, printed
pp.215–217. These inputs still require proof; their proofs must keep their
generator, norm-kernel character, actual unitarity, Galois pullback and
spectral hypotheses. The branch must construct those witnesses.
7. **Auxiliary supercuspidality.** Printed p.203 invokes
Henniart–Herb Proposition 5.5 after showing all actual local conjugates
distinct. Registered `henniart-herb-1995-induction`, printed
pp.152–153 (PDF indices21–22), gives the local κ-lift criterion.
`CyclicWeakInductionSupercuspidalStatement` is a derived global
consequence, not a verbatim local theorem. Its proof must identify
global induction locally with that κ-lift and identify any supplied
weak induction by strong multiplicity one. The prime branch must
first supply actual supercuspidal conjugate witnesses and their local
distinctness, comparing genuinely normalized monomial families at
common weight; forward comparison can then be used contrapositively.
8. **Singleton.** Printed p.203, TeX 1666–1674, refers to Lemma 1.6,
printed pp.188–189 (PDF12–13), TeX 687–794. The existing stable-descent
statement supplies weak descents and finite-twist classification.
The singleton branch also has to give actual ramified local descent and
supercuspidality reflection, finite-character correction to conjugate
self-duality, extension from the real subfield, and matching the
distinct descents with extensions of the irreducible monomial
restriction. This is why weak descent alone does not fit the complete
needed input. Theorem 1.7 assumes supercuspidality and cannot establish
it for an arbitrary descent. The complete branch is stated explicitly;
its proof must split these remaining obligations.
9. **Lemma 4.7.** The existing published theorem
`Langlands.Global.harrisGeneralPosition`, module
`Langlands.Global.Arithmetic.HarrisGeneralPositionProof`, proves
`HarrisGeneralPositionStatement` in arbitrary field universe, including
residue characteristic two. The theorem retains normalized
reciprocity explicitly. It constructs local general-position characters
and the indicated tower, not the global character/place transports of
the Mackey step. Those belong to that step.

## Four translation obligations

| Obligation | Present handling | Remaining work |
| --- | --- | --- |
| Missing sum in Definition1.3(b), p.186 | Built into published `Langlands.Automorphic.Unramified.WeakInduction.inducedEulerPolynomial`: product over all places above, representing the direct sum of the local induced parameters. The published actual weak-induction relation uses it. | The proofs of the prime and singleton branches must give their spectral attachments and the Euler relation for their actual output. |
| Mackey rank and p=2 in Lemma4.7 proof, pp.204–206 | Published `Langlands.Global.harrisGeneralPosition` uses actual finite-index Mackey induction and the first-order auxiliary-character proof covering p=2. New Mackey interfaces use `[D·a(E'):D]`, matching the inducing extension and rank-one base. | The Mackey step (proved: `proposition48MackeyStep`) gives the exact global child/rank and place transports. The local published proof alone does not prove them. |
| General-coefficient Theorem1.7 dependency, p.202 | Built into the derived `HarrisSupercuspidalLocalComparisonStatement` with arbitrary regular algebraic type, sourced to 1999 Theorem5.9(ii). | The comparison itself is open (the Library derives it from `Harris1999Theorem59iiParameterStatement` and `HarrisSupercuspidalRestrictionIrreducibleStatement`: `harrisSupercuspidalLocalComparison_of_canonical`); the prime branch must supply its common-weight normalized monomial witnesses. |
| Half-integral twists along induction, p.191 | Built into inherited-parity child validity, genuine CM base-character normalization and actual determinant untwisting; the reduction lists the two parity inputs separately. | The parity decomposition ([parity transport note](proposition-48-parity-transport.md)) gives the correction and transport; the branches must give their realizations and weight normalization. |

No `n < p` bound, stronger general-place ramified compatibility or
unproved multiplicity-one assertion is inserted.

## Status

The fourteen statement pairs of this reduction (the four internal data
modules, rank-one and full parity statements, auxiliary inputs, Mackey step,
invariance, prime and singleton branches, reduction, comparison and the
Henniart–Herb consequence) were checked byte for byte against Library commit
`f68324d1a21483563906b878776458c28ca83618`. The reduction first appeared at
`af5d652c2f2ff5b35b4ce4dbbf7cbec8bbf3e99e`; it compiles without diagnostics
and is a `Prop` with independent parameters `uF,uV`. Of the proofs, the
Library has the reduction (general and totally complex), the rank-one
statements, the Mackey step and isobaric invariance. Proposition 4.8 itself,
the two branches, the parity inputs and the external inputs (Theorem 1.2, the
comparison, rigidity, the Arthur–Clozel inputs and the Henniart–Herb
consequence) are open.
