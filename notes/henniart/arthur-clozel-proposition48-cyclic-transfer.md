# Arthur–Clozel cyclic transfer inputs to Harris Proposition 4.8

This note decomposes three cyclic transfer propositions and their totally complex
companions into named statements. The original
regular induction and stable descent propositions are in
`Langlands.Automorphic.Unramified.CyclicTransferStatement`, and the
regular orbit lift is in `Langlands.Automorphic.Unramified.IsobaricCyclicTransferStatement`.
The companions are in `Langlands.Automorphic.Unramified.CyclicTransferInputsTCStatement`.
Each proposition keeps independent field and presentation universes.
The Harris reductions use `.{0,0,uV,uV}`. [General cuspidal targets](../../Langlands/Automorphic/Unramified/CyclicTransferStatement.md), [isobaric targets](../../Langlands/Automorphic/Unramified/IsobaricCyclicTransferStatement.md), [totally complex targets](../../Langlands/Automorphic/Unramified/CyclicTransferInputsTCStatement.md)

## Use in Proposition 4.8

The prime-orbit branch in Harris (1998), pp. 202–203, assembles the upper
isobaric datum from a full orbit of distinct actual cuspidal classes.
Input 11, `CyclicRegularInductionStatement`, gives the lower cuspidal
weak induction used in that branch. Input 12,
`CyclicRegularOrbitLiftStatement`, identifies its singleton as the unique
unitary isobaric datum with that full orbit as weak base change. The
norm-kernel self-twist and the multiplied rank refer to the actual lower
class. The separate Henniart–Herb local supercuspidal comparison (supercuspidality at a
unique place of cyclic weak automorphic induction) is input 14.
[Prime branch](../../Langlands/Global/Arithmetic/HarrisProposition48PrimeBranchStatement.md)

In the singleton branch, the upper datum is a stable cuspidal class.
Input 13, `CyclicStableDescentStatement`, gives all its cuspidal descents
as the distinct determinant twists of one class by the powers of a
character with kernel exactly the idele-class norm image. These are the
classes available for matching the extensions of the Mackey constituent.
The totally complex reduction of Proposition 4.8 to its fourteen inputs,
`Proposition48ReductionTCStatement`, is proved, as `proposition48ReductionTC`
(`Langlands/Global/Arithmetic/HarrisProposition48ReductionTCProof.lean`). Its prime-orbit
and singleton branches are the separate statements `Proposition48PrimeBranchTCStatement`
and `Proposition48SingletonBranchTCStatement`; this note records no proof of them. The number fields in the
applications extend a CM base and are totally complex. [Singleton branch](../../Langlands/Global/Arithmetic/HarrisProposition48SingletonBranchStatement.md), [TC reduction and inputs](../../Langlands/Global/Arithmetic/HarrisProposition48ReductionTCStatement.md)

## Actual classes and unramified transfer

`CuspidalOperatorRealization.IsoClass` records the full actual cuspidal
operator class at a fixed positive rank. `IsobaricData` is a finite
multiset of positive-rank cuspidal classes. An attachment to these data
includes genuine presentations of the constituents, so a multiset of
numerical eigenvalues alone supplies no actual realization. Arithmetic
pullback transports the full operator class and reindexes attached
spectra by the induced equivalence of places. A finite-order determinant
twist acts on the actual class and scales its attached spectra at the
unramified places by the character evaluated at the local uniformizer.
Unitarity in the isobaric statement is constituentwise unitarizability.
An actual unitary central character supplies the unitary form on a
cuspidal realization via `isUnitarizable_of_hasUnitaryCentralCharacter`.
[Isobaric data](../../Langlands/Automorphic/IsobaricData.md), [Galois conjugation and weak transfer](../../Langlands/Automorphic/Unramified/IsobaricWeakTransfer.md), [actual spectral determinant twists](../../Langlands/Automorphic/CuspidalSpectralDeterminantTwist.md)

Weak base change at a retained place `v` raises every lower eigenvalue
to the residue degree at each `w` above `v`. Weak induction uses the
product of upper Euler denominator polynomials with `X` replaced by
`X^f(w/v)` and multiplies the rank by the field degree. All places above
one cofinite set of base places occur in these relations. These weak
relations give the cofinite finite-place assertions of the Harris inputs.
Input 14 supplies the induction comparison at the prescribed place
through the separate Henniart–Herb statement.
[Arithmetic weak transfer](../../Langlands/Representation/Unramified/WeakTransfer.md)

## Actual prime-degree realizations

Arthur and Clozel (1989), III.4.2(d)–(e), printed pp. 202–210, separates
stable cuspidal descent from realization of the full orbit of a regular
upper cusp. Each argument uses II.(17.8), pp. 197–198, in the form of
III.(4.1)–(4.2), p. 203. At fixed norm of the imaginary archimedean infinitesimal character
and fixed split-centre character, the untwisted discrete trace equals
the degree times the twisted discrete trace. With the source's
normalization it includes the regular Weyl terms of the proper Levis.
In (e) the equal rank blocks carry the orbit constituents. The cyclic
Weyl element, normalized intertwiner covariance, equality of reordered
traces and the Weyl coefficients give a nonzero isolated contribution.
Matching the good-place Hecke tests isolates a lower automorphic
subquotient. The rank induction on cuspidal support and the partial
Rankin–Selberg comparison in III.4.3 and (4.5) force it to be cuspidal.

This analytic prerequisite consists of the actual discrete distributions, test matching,
Hecke extraction and a joint rank induction with (a)–(b) on strictly
smaller ranks. Its interfaces are stated in the Library (see “Reused results and analytic
prerequisites” below); this note records no proof of it. For a totally complex base all
infinite places split,
and the matching there is cyclic convolution on the split complex
factors with compatible measures. The same finite matching and
proper-Levi terms enter. The general route additionally treats the
nonsplit real-place cases of test matching. The global automorphic program
([global program coverage](../automorphic/global-program-coverage.md)) supplies the general
object and analytic foundations and the actual GL_n comparisons. The related
simple trace comparison and the local B4–B7 inputs (the simple trace formula with its twisted
form, and local cyclic base change of prime degree) are separate prerequisites; the existing
spherical matching and abstract character separation results are reused where applicable.
The same prerequisite includes the totally complex singleton existence
consequence of (a)–(b). A supplied unitarizable lower cusp has a unitary
isobaric weak base change given by the upper cusp in (a) or the full orbit
in (b), with actual attached spectra and independent field and presentation
universes. The constituentwise assembly in III.4.2(c) (prime cyclic unitary isobaric base
change over totally complex fields) uses this consequence and Euler constituent recovery.

## Common arithmetic and Rankin–Selberg comparisons

The norm quotient is cyclic of order `d = [E:F]` and the powers of any
faithful norm-kernel character exhaust the norm-trivial characters.
On the unramified cofinite set, III.3.1, p. 201, uses the stronger local
fact that `η_v(ϖ_v)` has exact order `f(w/v)`. The relative Weil transfer
sends a local degree-one element to the inverse uniformizer class.
The Galois projection has order `f(w/v)`. Its factor through the transfer
has the norm kernel, so faithfulness and inversion preserve the exact
order. [Global norm-kernel character](../../Langlands/Global/Arithmetic/CyclicNormKernelCharacterProof.md), [local order](../../Langlands/Global/Arithmetic/CyclicNormKernelUnramifiedOrderStatement.md)

For a supplied pair of weak base changes between unitary data, take the
contragredient in the second variable. At a good base place with residue
degree `f`, for every quotient `a` of eigenvalues the factor over the
`d` norm twists is `(1 - a^f X^f)^(d/f)`. The residue cardinalities and
the `d/f` actual places above `v` identify this with the upper factor.
Absolute convergence in the right half-plane and meromorphic continuation
identify the products for a common finite omission set. III.(2.1)–(2.3),
III.3.1 and III.4.3, pp. 199–201, 204, convert the orders at one into
counts of equal pairs of actual constituents. The multiset count keeps
both multiplicities. The resulting unitary cuspidal pair has order `−1` for equal classes and order zero otherwise.
This uses a partial pole and nonvanishing result at one for the actual
attached pair factors. [Pair multiplicity statement](../../Langlands/Automorphic/Unramified/CyclicWeakBaseChangePairMultiplicityStatement.md)

## Regular induction and orbit-lift reductions

The forward arithmetic comparison uses the fact that the decomposition
group at an unramified upper place has size `f`. The full orbit spectrum
at this place is the union of the spectra at all places above `v`, each
taken `f` times. Raising the roots from weak induction to their `f`-th
powers gives this same multiset. The reverse comparison needs fixation
of the actual lower class by `η`. Its attached spectrum is invariant
under multiplication by a primitive `f`-th root of unity. Powering to
`f` and cancelling the common multiplicity recovers the weak induction
polynomial. These are the two finite-place comparisons from III.(1.1)
and III.6.1–6.2, pp. 199, 214–217. In a tower, multiplication of residue
degrees composes the polynomial substitutions and the indices reassemble
by contraction of places. [Orbit and induction comparisons](../../Langlands/Automorphic/Unramified/CyclicOrbitInductionComparisonStatement.md), [induction by stages](../../Langlands/Automorphic/Unramified/WeakInductionTransitivityStatement.md)

For arbitrary degree, choose a prime top layer. The prime regular-orbit
realization has a lower singleton with unitary central character. Comparing
its self-pair with the upper orbit self-pair forces every norm-character
power to fix the lower class, since the upper orbit has exactly as many
equal pairs as there are twists. The reverse comparison gives weak
induction. If a nonidentity quotient automorphism fixed the intermediate
class, lift it to the top Galois group. Weak base-change equivariance
makes its conjugate prime orbit another weak base change of the same
class. The upper cofinite Euler factors agree, and constituent recovery
identifies the two orbits. This forces a nonidentity automorphism of
the upper field to stabilize the original class. The contradiction treats
all nonidentity powers. Induction by stages and the degree-one transport
case give the existence step of III.6.4. [Actual regular induction existence](../../Langlands/Automorphic/Unramified/CyclicRegularInductionExistenceStatement.md)

For input 11, the induced Euler denominator is invariant under the
local norm-character scaling. The published actual twist attachment and
Euler constituent recovery identify the twist with the original lower
class. For any cuspidal competitor, the independent upper presentations
of the same cusp agree on a cofinite set, so both lower inductions have
the same Euler factors. The singleton recovery applies to the competitor
in the full scope of the target. [Regular induction reduction](../../Langlands/Automorphic/Unramified/CyclicRegularInductionReductionStatement.md)

For input 12, take the forward weak base change of the unitary singleton.
The orbit self-pair gives the norm self-twist. For a second unitary lower
datum weakly lifting to the same orbit, the pair formula gives `d` times
the multiplicity of the witness class in that datum. The upper count is
`d`, so the multiplicity is one. Equality of total rank and positive
constituent ranks identify the entire datum with the singleton. The
forward comparison provides the converse implication of the target.
[Regular orbit-lift reduction](../../Langlands/Automorphic/Unramified/CyclicRegularOrbitLiftReductionStatement.md)

## Stable descent reduction

Begin with the actual stable prime realization of III.4.2(d). In
composite degree, choose a bottom prime step `K/F` of degree `p` and
descend from `E` to `K` by induction. Comparing that unitary cusp with
its conjugate by the bottom generator uses weak base-change equivariance
and III.3.1. The resulting character `χ` of `K` is trivial on the norms
from `E` and invariant under the bottom generator. Natural transport of
determinant twists then gives a self-twist by `χ^p`. A pair count for the
cuspidal weak lift to `E` shows that only the identity norm twist fixes
the intermediate class. Consequently `χ^p = 1`. A nontrivial `χ` would
restrict to a character faithful on the bottom norm quotient, which is
excluded by the prime twisted-cuspidal obstruction. The resulting
stability lets the bottom prime descent proceed, and weak base change
composes in the tower. [Stable descent reduction](../../Langlands/Automorphic/Unramified/CyclicStableDescentReductionStatement.md)

The original proof of III.6.3, p. 217, needs the stability of the
intermediate prime descendant. The obstruction is the prime finite-order
case of Clozel–Rajan, *Solvable base change*, Theorem 1, p. 2, with the
cyclic descent argument at the end of §2, p. 7. The stabilized
character-twisted discrete comparison and spectral support calculation
of §§4–7 are a separate prerequisite; this note records no proof of them. They use ordinary and proper-Levi terms and a finite character
twist, with the split complex archimedean comparison in the totally
complex case. [Clozel–Rajan preprint](https://arxiv.org/abs/1806.02513v1)

For the complete fibre of input 13, compare each competing cuspidal
class to the witness by III.3.1, at its full scope for arbitrary actual
cuspidal classes. Norm-character classification gives all the powers of
the supplied `η`, and norm-twist compatibility with weak base change
gives the converse. For the unitary witness, the self-pair comparison
gives the single identity contribution upstairs and downstairs. Distinctness
of the norm powers as twists follows. This proves all parts of the exact
stable descent proposition once the named reduction and inputs have
proofs, including the degree-one field equivalence case.

## Statements and their proofs

The six exact targets, six conditional reduction propositions and the
other entries marked as statements were checked to be in the Library at commit
`59f998392b3e63e0ccafb68014f9bbcfdd17c73e`. Of their proofs, the Library proves the
orbit-lift reduction `cyclicRegularOrbitLiftReduction`, the unramified order of the norm-kernel
character `cyclicNormKernelUnramifiedOrder`, and the reductions of the joint rank induction
(`cyclicPrimeJointRankInductionReduction`, `cyclicPrimeJointRankInductionReductionTC`); this
note records no proof of the other statements below (searched by statement name). A
conditional reduction proves the implication
with its premises supplied; proofs of those premises then give the unconditional targets. The
tables use the `Langlands.Automorphic.Unramified` namespace except where shown.

### Exact Harris inputs and conditional reductions

| Harris input | Exact target | Conditional reduction | Premises for the assembly |
| --- | --- | --- | --- |
| 11 | `CyclicRegularInductionStatement` | `CyclicRegularInductionReductionStatement` | Regular induction existence, local norm-character order and Euler constituent recovery. |
| 11, totally complex | `CyclicRegularInductionTCStatement` | `CyclicRegularInductionReductionTCStatement` | TC regular induction existence, local norm-character order and TC Euler constituent recovery. |
| 12 | `CyclicRegularOrbitLiftStatement` | `CyclicRegularOrbitLiftReductionStatement` (proved, as `cyclicRegularOrbitLiftReduction`) | Regular induction existence, forward orbit comparison and pair multiplicity. |
| 12, totally complex | `CyclicRegularOrbitLiftTCStatement` | `CyclicRegularOrbitLiftReductionTCStatement` | TC regular induction existence, forward orbit comparison and TC pair multiplicity. |
| 13 | `CyclicStableDescentStatement` | `CyclicStableDescentReductionStatement` | Prime stable descent, prime twisted obstruction, pair multiplicity and shared descent inputs. |
| 13, totally complex | `CyclicStableDescentTCStatement` | `CyclicStableDescentTCReductionStatement` | TC prime stable descent, TC twisted obstruction, TC pair multiplicity and shared descent inputs. |

The regular induction, orbit-lift and stable reduction pairs are stated in the modules linked
below. The shared descent
inputs are the cuspidal fibre, prime norm-character restriction, weak
base-change tower and equivariance, determinant twist under comap,
norm-twist preservation of weak base change, attachment existence and
spectral comap. Although each stable reduction has nineteen premises
at several universe instantiations, one proof of each shared input at
its stated universe scope serves every occurrence. Both stable descent
reductions use the unrestricted cuspidal fibre. The TC stable descent
reduction uses split complex matching for the two prime trace inputs.
[Induction reduction](../../Langlands/Automorphic/Unramified/CyclicRegularInductionReductionStatement.md), [orbit-lift reduction](../../Langlands/Automorphic/Unramified/CyclicRegularOrbitLiftReductionStatement.md), [stable descent reduction](../../Langlands/Automorphic/Unramified/CyclicStableDescentReductionStatement.md)

### Arithmetic, spectral and realization statements

| Statement | Source and inputs | Proof in the Library |
| --- | --- | --- |
| `Langlands.Global.HeckeCharacter.CyclicNormKernelUnramifiedOrderStatement` | AC III.3.1 and III.6.1–6.2, pp. 201, 214–217. | `cyclicNormKernelUnramifiedOrder` (`Langlands/Global/Arithmetic/CyclicNormKernelUnramifiedOrderProof.lean`) |
| `WeakInductionTransitivityStatement` | AC III.6.1–6.2, pp. 214–215. | none recorded |
| `WeakInductionOrbitBaseChangeStatement` | AC III.(1.1) and III.6.1–6.2, pp. 199, 214–217. The prime-degree specialization is the separate `CyclicInductionOrbitBaseChangeStatement`. [Prime specialization](../../Langlands/Automorphic/Unramified/CyclicInductionOrbitBaseChangeStatement.md) | none recorded |
| `CyclicOrbitBaseChangeWeakInductionStatement` | AC III.(6.5)–(6.6) and the root comparison, pp. 214–217. | none recorded |
| `CyclicWeakBaseChangePairMultiplicityStatement`, `CyclicWeakBaseChangePairMultiplicityTCStatement` | AC III.(2.1)–(2.3), III.3.1, III.4.2–4.3, pp. 199–210. Uses local norm-character order, partial pair L-function existence and partial order at one. | none recorded |
| `CyclicPrimeRegularOrbitRealizationStatement`, `CyclicPrimeRegularOrbitRealizationTCStatement` | AC III.4.2(e), pp. 202, 207–210, with the discrete comparison and analytic rank step of III.4.2 (below). | none recorded |
| `CyclicRegularInductionExistenceStatement`, `CyclicRegularInductionExistenceTCStatement` | AC III.4.2(e), III.4.4(iii), III.6.1–6.2 and III.6.4, pp. 202, 207–218. | none recorded |
| `CyclicPrimeStableCuspidalDescentStatement`, `CyclicPrimeStableCuspidalDescentTCStatement` | AC III.4.2(d), pp. 202, 206–207, with the discrete comparison and analytic rank step of III.4.2 (below). | none recorded |
| `CyclicPrimeTwistedCuspidalObstructionStatement`, `CyclicPrimeTwistedCuspidalObstructionTCStatement` | CR Theorem 1, (4.2), Propositions 4–5, Lemma 5 and §7.3, with the character-twisted comparison of CR §§4–7. | none recorded |
| `Langlands.Global.CuspidalPartialPairOrderOneStatement` | AC III.(2.2)–(2.3), p. 200, and JS II (3.3), (3.6)–(3.7), pp. 795, 798–804. [Partial pair orders](../../Langlands/Global/Factors/CuspidalPartialPairOrderOneStatement.md) | none recorded |
| `CuspidalSpectralArithmeticComapStatement` | AC III.1.1 and III.4.4(iii), pp. 199, 210–211. The route uses the published actual arithmetic spectral transport and matches the specified place reindexing. | none recorded |
| `CuspidalSpectralAttachmentExistenceStatement` | Flath §§2–3, Theorem 3, pp. 180–182, and AC III.1.1, p. 199. The route resizes the local factors of the published actual finite-slice construction to the specified universe. | none recorded |
| `IsobaricWeakBaseChangeTowerStatement`, `IsobaricWeakBaseChangeEquivarianceStatement` | AC III.1.1, III.4.4(iii), III.6.2–6.3, pp. 199, 210–211, 216–217. | none recorded |
| `Langlands.Global.HeckeCharacter.CyclicPrimeNormCharacterRestrictionStatement` | AC III.3–4, pp. 201–202, and CR Theorem 1 and §2, pp. 2, 7. Uses the actual idèle-class norm tower, Galois product and inclusion power. | none recorded |
| `CuspidalWeakBaseChangeNormTwistStatement`, `CuspidalDeterminantTwistArithmeticComapStatement` | AC III.1.1 and III.6.3, pp. 199, 217, and CR §§1.1, 2, pp. 2, 6–7. | none recorded |

### Reused results and analytic prerequisites

- `CyclicCuspidalFiberStatement` is the published III.3.1 proposition; this note records no
  proof of it. The Library includes the conditional `cyclicCuspidalFiberReduction`
  (`Langlands/Automorphic/Unramified/CyclicCuspidalFiberReduction.lean`). Its first premise is
  `CuspidalPairBoundaryNonvanishingStatement` (this note records no unconditional proof of it; the Library derives it from `CuspidalPairBoundaryNonvanishingEnlargedStatement` by `cuspidalPairBoundaryNonvanishingReduction`). The proof
  uses both conjuncts
  to obtain the meromorphic partial pair L-functions and bound the
  orders of the self-pair product's factors at `1` above by zero. The
  other premises are cofinite norm-kernel local order (`CyclicNormKernelUnramifiedOrderStatement`,
  proved) and exact same-rank partial pair orders at `1` (`CuspidalPartialPairOrderOneStatement`).
  The proof uses
  common real norm-power normalization and actual contragredient and
  twist presentations. The pair-multiplicity route uses partial
  pair L-function existence, local norm-character order and partial
  pair orders in the constituentwise unitary case.
  [Exact fibre statement](../../Langlands/Automorphic/Unramified/CyclicCuspidalFiberStatement.md), [conditional fibre proof](../../Langlands/Automorphic/Unramified/CyclicCuspidalFiberReduction.md), [boundary nonvanishing](../../Langlands/Global/Factors/CuspidalPairBoundaryNonvanishingStatement.md)
- The completed-to-partial route to `CuspidalPartialPairOrderOneStatement` uses the completed
  poles (`CuspidalPairPoleStatement`), boundary nonvanishing
  and continuation (`CuspidalPairBoundaryNonvanishingStatement`), the published
  `cuspidalFinitePairRegularity`,
  and archimedean pair regularity (`CuspidalArchimedeanPairRegularityStatement`). In the totally complex
  applications only complex local factors occur. For an actual
  unitarizable constituent the unitary central character follows from
  the central translation law, real-skew invariance and compact
  norm-one idèle classes. This permits use of the actual cuspidal pair
  order in the multiset count.
  [Partial pair order hypotheses](../../Langlands/Global/Factors/CuspidalPartialPairOrderOneStatement.md)
- Euler constituent recovery in both field scopes is part of `CuspidalSpectralRigidityStatement`
  and its totally complex form (this note records no unconditional proof). The published
  `cuspidalSpectralRigidityLandauReduction` gives the full rigidity
  conjunction in each scope from `CuspidalPairAbsoluteConvergenceStatement`
  and the corresponding completed pole input, `CuspidalPairPoleStatement`
  or `CuspidalPairPoleTCStatement`. It obtains the logarithmic limit and
  all-power trace independence, then derives trace and Euler constituent
  recovery as in JS II 4.1–4.2 and 4.4, pp. 805–807, 809. The exact
  induction proof uses recovery for the arbitrary cuspidal competitor,
  including nonunitary classes. [Landau reduction](../../Langlands/Automorphic/Unramified/CuspidalSpectralRigidityLandauReduction.md), [TC rigidity](../../Langlands/Automorphic/Unramified/CuspidalSpectralRigidityTCStatement.md)
- The Library proves
  `cuspidalPairAbsoluteConvergence_of_selfPairContinuation` and
  `cuspidalSelfPairContinuation`,
  which supplies its premise at the same universes. This leaves the
  completed pole input for each scope (`CuspidalPairPoleStatement`, `CuspidalPairPoleTCStatement`;
  this note records no unconditional proof) and the exact rigidity assembly.
  [Absolute convergence](../../Langlands/Global/Factors/CuspidalPairAbsoluteConvergenceProof.md), [self-pair continuation](../../Langlands/Global/Factors/CuspidalSelfPairContinuationProof.md), [completed poles](../../Langlands/Global/Factors/CuspidalPairPoleStatement.md), [TC completed poles](../../Langlands/Global/Factors/CuspidalPairPoleTCStatement.md)
- `Langlands.Global.HeckeCharacter.cyclicNormKernelCharacter` is a
  published proof. The local unramified
  order and tower restriction are the separate statements in the table (the first is proved).
  [Norm-kernel character proof](../../Langlands/Global/Arithmetic/CyclicNormKernelCharacterProof.md)
- `Langlands.Automorphic.cuspidalArithmeticSpectralTransport` and
  `CuspidalSpectralPresentation.arithmeticComap` are published proofs. The route to
  `CuspidalSpectralArithmeticComapStatement` uses this
  transport to identify the reindexed spectral system for the
  prescribed arithmetic comap. The route to `CuspidalSpectralAttachmentExistenceStatement` reuses
  `cuspidalIrreducibleAdmissibleFiniteSliceExistence`,
  `CuspidalOperatorRealization.exists_presentation_of_finiteSlice`
  and `CuspidalSpectralUniverseLift` from the existing construction. [Arithmetic spectral transport proof](../../Langlands/Automorphic/CuspidalArithmeticSpectralTransportProof.md)
- The full ordinary and twisted discrete comparison, including
  proper-Levi terms, Hecke isolation and the analytic step of joint
  strict-rank induction in AC III.4.2(a), (b), (d) and (e), is the analytic prerequisite above.
  The published `CyclicPrimeJointRankInductionStatement` module
  gives both scopes of the
  rank step, the all-ranks result and the reduction of the latter to
  the former. The Library proves the reductions (`cyclicPrimeJointRankInductionReduction`,
  `cyclicPrimeJointRankInductionReductionTC`); this note records no proof of the rank step. The
  going-up part yields
  `CyclicPrimeCuspidalBaseChangeExistenceTCStatement`, the input of the assembly
  of III.4.2(c). The induction
  applies going up or down only at strictly smaller ranks.
  [Joint rank induction](../../Langlands/Automorphic/Unramified/CyclicPrimeJointRankInductionStatement.md), [TC singleton base change](../../Langlands/Automorphic/Unramified/CyclicPrimeCuspidalBaseChangeExistenceTCStatement.md)
- `Langlands.BaseChange.FinitePlaceFullMatchingStatement` states both directions of full
  finite-place matching in AC I.3.1, p. 20. AC I.4 concerns unramified
  spherical matching. `Langlands.BaseChange.SplitArchimedeanMatchingStatement`
  and `Langlands.BaseChange.NonsplitRealMatchingStatement` are stated in one module. The
  former gives
  the split convolution of AC I.5 (5.1)–(5.2), pp. 48–49, which the TC
  comparison uses at complex places. The latter gives AC I.7.3,
  pp. 73–74, for the unrestricted comparison.
  [Finite matching](../../Langlands/BaseChange/FinitePlaceFullMatchingStatement.md), [archimedean matching](../../Langlands/BaseChange/ArchimedeanLocalMatchingStatement.md)
- `Langlands.TraceFormula.CyclicSplitCenterMeasureStatement` and
  `Langlands.TraceFormula.CyclicEqualBlockLeviCountStatement` are stated. The compatible measures
  and equal-block Weyl count enter both scopes of the comparison in
  II.(17.7)–(17.8) and the proper-Levi calculation of III.4.2. [Split-centre measure](../../Langlands/TraceFormula/CyclicSplitCenterMeasureStatement.md), [Weyl weights](../../Langlands/TraceFormula/CyclicDiscreteWeylWeights.md)
- The finite character-twisted trace
  comparison, endoscopic support and spectral detection of CR §§4–7,
  PDF pp. 10–26, are a separate prerequisite; this note records neither its statement nor its
  proof. The stabilized distribution
  contains the cuspidal,
  residual and regular proper-Levi terms. The exact obstruction statements use this comparison
  in the unrestricted and totally complex scopes.

## Sources

Primary sources are `arthur-clozel-1989-base-change` (1989), and
`harris-1998-local-langlands` (1998), Proposition 4.8, printed pp. 202–203.
Arthur–Clozel page references are printed pages, with PDF offset 14.
The composite stability correction uses
`clozel-rajan-2018-solvable-base-change` (arXiv:1806.02513v1).
JS II is Jacquet and Shalika (1981), *On Euler Products and the
Classification of Automorphic Representations II*. Flath's presentation
input is *Decomposition of Representations into Tensor Products*,
Theorem 3. The paired Markdown gives the source references and
the statement scopes.
