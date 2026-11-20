# Arthur–Clozel cyclic transfer inputs to Harris Proposition 4.8

Task 6699 `ca76241a-30bc-46d4-a0b9-5f6c284363a5` decomposes three cyclic
transfer propositions and their totally complex companions. The original
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
class. The separate Henniart–Herb local supercuspidal comparison is input
14, owned by Task 6845 `3064d640-8ebf-4ac1-807c-a48f48d653c4`.
[Prime branch](../../Langlands/Global/Arithmetic/HarrisProposition48PrimeBranchStatement.md)

In the singleton branch, the upper datum is a stable cuspidal class.
Input 13, `CyclicStableDescentStatement`, gives all its cuspidal descents
as the distinct determinant twists of one class by the powers of a
character with kernel exactly the idele-class norm image. These are the
classes available for matching the extensions of the Mackey constituent.
The totally complex reduction proof belongs to Task 7213
`b517f901-0ac4-4ae4-a08e-b8b88a3b0fec`. Its prime and singleton proof
decompositions belong to Tasks 7221 `528311c0-f3fd-4553-ad48-a6bed4282b5a`
and 7222 `95f79351-962f-4e98-a877-d3ca1aa759e1`. The number fields in the
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

Task 7868 `e49b1501-66f5-4b5f-9757-fcc4f1f7fad8` owns this analytic
prerequisite, including the actual discrete distributions, test matching,
Hecke extraction and a joint rank induction with (a)–(b) on strictly
smaller ranks. For a totally complex base all infinite places split,
and the matching there is cyclic convolution on the split complex
factors with compatible measures. The same finite matching and
proper-Levi terms enter. The general route additionally treats the
nonsplit real-place cases of test matching. The spectral program
`34b81620-20d7-4059-9b08-6bedd1c1c029` supplies the general object and
analytic foundations and the actual GL_n comparisons. The related
simple trace comparison and the local B4–B7 inputs belong to Task 7340
`0407c885-1c0b-496b-a8bf-829f3c1a7038`; the existing spherical matching
and abstract character separation owners are reused where applicable.
Task 7868 revision 2 also assigns the totally complex singleton existence
consequence of (a)–(b). A supplied unitarizable lower cusp has a unitary
isobaric weak base change given by the upper cusp in (a) or the full orbit
in (b), with actual attached spectra and independent field and presentation
universes. Task 7860 `835f1bf4-f1d3-4a52-ac52-54475877d275` uses this
consequence for constituentwise assembly in III.4.2(c) and uses Task 6446
for Euler constituent rigidity.

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
cyclic descent argument at the end of §2, p. 7. Task 7866
`baaddc1e-26c5-41f7-8ebc-fe5c6e08a21b` owns the stabilized
character-twisted discrete comparison and spectral support calculation
of §§4–7. It uses ordinary and proper-Levi terms and a finite character
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

## Proof ownership and publication status

This inventory records Library `59f998392b3e63e0ccafb68014f9bbcfdd17c73e`.
The six exact targets, six conditional reduction propositions and the
other entries marked as statements are published. Their exact proofs
remain open. The owners of a conditional reduction prove the implication
with its premises supplied. The owners of the exact Harris inputs use
proofs of those premises to prove the unconditional targets. The tables
use the `Langlands.Automorphic.Unramified` namespace except where shown.

### Exact Harris inputs and conditional reductions

| Harris input | Published exact target and proof owner | Published conditional reduction and proof owner | Premises for the assembly |
| --- | --- | --- | --- |
| 11 | `CyclicRegularInductionStatement`, Task 7877 `8cbdd474-0e1f-46cf-867b-181d2ff3cc5a` | `CyclicRegularInductionReductionStatement`, Task 7938 `8c1adfd1-2662-49b1-8d0c-f6455de044f5` | Regular induction existence, local norm-character order and Euler constituent recovery. |
| 11, totally complex | `CyclicRegularInductionTCStatement`, Task 7940 `3a690d1f-2e72-473e-87fd-a1c1ecb2aebb` | `CyclicRegularInductionReductionTCStatement`, Task 7938 `8c1adfd1-2662-49b1-8d0c-f6455de044f5` | TC regular induction existence, local norm-character order and TC Euler constituent recovery. |
| 12 | `CyclicRegularOrbitLiftStatement`, Task 7878 `14fc872d-a435-4355-97b3-5e68c8da79d1` | `CyclicRegularOrbitLiftReductionStatement`, Task 7939 `72357d8a-ab3f-4bd8-8f19-180337b2388f` | Regular induction existence, forward orbit comparison and pair multiplicity. |
| 12, totally complex | `CyclicRegularOrbitLiftTCStatement`, Task 7941 `ad952a89-0aaf-4cd8-9fa6-478abc7f97bf` | `CyclicRegularOrbitLiftReductionTCStatement`, Task 7939 `72357d8a-ab3f-4bd8-8f19-180337b2388f` | TC regular induction existence, forward orbit comparison and TC pair multiplicity. |
| 13 | `CyclicStableDescentStatement`, Task 7876 `2b279fcd-732d-40b5-a66e-e51e6b7f8bc4` | `CyclicStableDescentReductionStatement`, Task 8119 `a46c1370-ce95-4f13-8ffd-814014d24a8c` | Prime stable descent, prime twisted obstruction, pair multiplicity and shared descent inputs. |
| 13, totally complex | `CyclicStableDescentTCStatement`, Task 8122 `f3ce66a4-d655-41f1-83bd-de93c83bf5fd` | `CyclicStableDescentTCReductionStatement`, Task 8120 `569a1aa0-bad5-4ac6-bfed-71acc138bc0e` | TC prime stable descent, TC twisted obstruction, TC pair multiplicity and shared descent inputs. |

The regular induction, orbit-lift and stable reduction pairs are published
in `78779cb8-701a-4b89-a3d7-b3c274f264b0`,
`2503077d-6242-487e-8775-64d8db52139d` and
`df623599-c382-48d5-98a7-05f7480488be`, respectively. The shared descent
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

| Published declaration | Publication | Open proof owner and source |
| --- | --- | --- |
| `Langlands.Global.HeckeCharacter.CyclicNormKernelUnramifiedOrderStatement` | `70e184a4-ad0f-4ee6-8d97-4b73ad62b13c` | Task 7931 `30ca335d-35fa-4667-8825-4a210cec9a3f`, AC III.3.1 and III.6.1–6.2, pp. 201, 214–217. |
| `WeakInductionTransitivityStatement` | `34d11c27-778d-4368-8348-89851d817606` | Task 7932 `997752e6-d555-4668-a323-acf4a3b41b3f`, AC III.6.1–6.2, pp. 214–215. |
| `WeakInductionOrbitBaseChangeStatement` | `86289f70-34ef-4661-8554-5d1d56a0d70b` | Task 7933 `05667613-b9a5-4b7a-80a8-b65b97762222`, AC III.(1.1) and III.6.1–6.2, pp. 199, 214–217. Task 7954 `151e25bb-d43d-4f45-b2c5-f96ef0bd6b13` owns the separate prime-degree specialization `CyclicInductionOrbitBaseChangeStatement`. [Prime specialization](../../Langlands/Automorphic/Unramified/CyclicInductionOrbitBaseChangeStatement.md) |
| `CyclicOrbitBaseChangeWeakInductionStatement` | `86289f70-34ef-4661-8554-5d1d56a0d70b` | Task 7934 `6b91d29f-bc41-44d2-98d6-fa35b51e74aa`, AC III.(6.5)–(6.6) and the root comparison, pp. 214–217. |
| `CyclicWeakBaseChangePairMultiplicityStatement`, `CyclicWeakBaseChangePairMultiplicityTCStatement` | `68528d6f-8fa5-4407-8231-bb7f8f320dc1` | Task 7935 `31dd20f3-0255-46cc-842b-db3591429703`, AC III.(2.1)–(2.3), III.3.1, III.4.2–4.3, pp. 199–210. Uses local norm-character order, partial pair L-function existence and partial order at one. |
| `CyclicPrimeRegularOrbitRealizationStatement`, `CyclicPrimeRegularOrbitRealizationTCStatement` | `eb9112c4-ee25-48a4-80c3-94519d19a558` | Task 7936 `db254bef-dfcc-4246-b9f5-dbfa219a01ed`, AC III.4.2(e), pp. 202, 207–210, with Task 7868's discrete comparison and analytic rank step. |
| `CyclicRegularInductionExistenceStatement`, `CyclicRegularInductionExistenceTCStatement` | `56e4db6f-2821-4314-bc5b-7dbf0b3fd854` | Task 7937 `4c9c6068-79f4-43ba-9403-08530405aaef`, AC III.4.2(e), III.4.4(iii), III.6.1–6.2 and III.6.4, pp. 202, 207–218. |
| `CyclicPrimeStableCuspidalDescentStatement`, `CyclicPrimeStableCuspidalDescentTCStatement` | `f599a084-6d71-47f1-9f09-677bde89e8c6` | Tasks 7975 `6917d16a-c39a-4420-b1a4-6080442ece6f` and 7977 `9237a41b-264a-4265-8c5f-a21c8b95077f`, AC III.4.2(d), pp. 202, 206–207, with Task 7868's discrete comparison and analytic rank step. |
| `CyclicPrimeTwistedCuspidalObstructionStatement`, `CyclicPrimeTwistedCuspidalObstructionTCStatement` | `fc16742c-daec-4edc-8b25-cb09ae15d473` | Tasks 7985 `d3ea2809-25f0-45f3-a6ef-0fa2d6cc15f4` and 7990 `491a203f-9419-44b5-a88f-986fd5b7ddbb`, CR Theorem 1, (4.2), Propositions 4–5, Lemma 5 and §7.3, with Task 7866's character-twisted comparison. |
| `Langlands.Global.CuspidalPartialPairOrderOneStatement` | `a722fd38-7bdd-4014-825c-1cfb6915713b` | Task 7965 `6c16a7c2-336a-43f1-9fa5-0c0c11fce108`, AC III.(2.2)–(2.3), p. 200, and JS II (3.3), (3.6)–(3.7), pp. 795, 798–804. [Partial pair orders](../../Langlands/Global/Factors/CuspidalPartialPairOrderOneStatement.md) |
| `CuspidalSpectralArithmeticComapStatement` | `48c8a73f-bae0-4b44-a266-16719f80fb76` | Task 7970 `0d9fe366-8d19-4cef-8f6b-f6e9ea2cb9aa`, AC III.1.1 and III.4.4(iii), pp. 199, 210–211. Use the published actual arithmetic spectral transport and match the specified place reindexing. |
| `CuspidalSpectralAttachmentExistenceStatement` | `45b75703-c32c-461c-95e5-f52042c3ad` | Task 7973 `3447caa8-4363-4545-aba1-9c9e2387282c`, Flath §§2–3, Theorem 3, pp. 180–182, and AC III.1.1, p. 199. Resize the local factors of the published actual finite-slice construction to the specified universe. |
| `IsobaricWeakBaseChangeTowerStatement`, `IsobaricWeakBaseChangeEquivarianceStatement` | `5cd7aba3-9fa3-493b-97ec-959c2ff5128f` | Tasks 8001 `d70b29e3-6384-4a06-ba48-654067b23b2c` and 8003 `661790bf-9e50-4ae8-8d20-f2f98f26c889`, AC III.1.1, III.4.4(iii), III.6.2–6.3, pp. 199, 210–211, 216–217. |
| `Langlands.Global.HeckeCharacter.CyclicPrimeNormCharacterRestrictionStatement` | `472a14b6-0345-4c1a-a908-eadaed083d54` | Task 8115 `a7412e66-e7c4-47b0-9a62-f883dbae6bca`, AC III.3–4, pp. 201–202, and CR Theorem 1 and §2, pp. 2, 7. Uses the actual idèle-class norm tower, Galois product and inclusion power. |
| `CuspidalWeakBaseChangeNormTwistStatement`, `CuspidalDeterminantTwistArithmeticComapStatement` | `65ebf039-667e-4355-832a-75bae7c8dab8` | Tasks 8116 `129633d2-3378-4ed4-8af2-b7dc4664eef6` and 8117 `2dc02aef-bb4c-46de-aaa0-32e4f74af14e`, AC III.1.1 and III.6.3, pp. 199, 217, and CR §§1.1, 2, pp. 2, 6–7. |

### Reused results and analytic prerequisites

- `CyclicCuspidalFiberStatement` is the published III.3.1 proposition.
  Task 7873 `b08ba858-b20b-465d-b9f8-411e612bf93c` owns the open exact proof.
  The Library includes `cyclicCuspidalFiberReduction` in publication
  `e82028e2-de0c-477d-9c9d-58a5f0d31468`. Its first premise is
  `CuspidalPairBoundaryNonvanishingStatement`, owned by Task 5816
  `c325654f-b8fb-4a43-9caf-c147e4ae95f2`. The proof uses both conjuncts
  to obtain the meromorphic partial pair L-functions and bound the
  orders of the self-pair product's factors at `1` above by zero. The
  other premises are cofinite norm-kernel local order (Task 7931) and
  exact same-rank partial pair orders at `1` (Task 7965). The proof uses
  common real norm-power normalization and actual contragredient and
  twist presentations. The pair-multiplicity route uses partial
  pair L-function existence, local norm-character order and partial
  pair orders in the constituentwise unitary case.
  [Exact fibre statement](../../Langlands/Automorphic/Unramified/CyclicCuspidalFiberStatement.md), [conditional fibre proof](../../Langlands/Automorphic/Unramified/CyclicCuspidalFiberReduction.md), [boundary nonvanishing](../../Langlands/Global/Factors/CuspidalPairBoundaryNonvanishingStatement.md)
- Task 7965's completed-to-partial route uses the completed poles
  (Task 5921 `786d8bc1-6a9b-4fa0-ae6c-89e17489000c`), boundary nonvanishing
  and continuation (Task 5816), published `cuspidalFinitePairRegularity`,
  and archimedean pair regularity (Task 7005
  `1a9d552f-6429-45fa-afcd-7f2806c4312f`). In the totally complex
  applications only complex local factors occur. For an actual
  unitarizable constituent the unitary central character follows from
  the central translation law, real-skew invariance and compact
  norm-one idèle classes. This permits use of the actual cuspidal pair
  order in the multiset count.
  [Partial pair order hypotheses](../../Langlands/Global/Factors/CuspidalPartialPairOrderOneStatement.md)
- Euler constituent recovery in both field scopes remains with Task 6446
  `c4f0be57-1a49-4a42-b813-4354e297ab3f`. The published
  `cuspidalSpectralRigidityLandauReduction`
  (`377e1c8e-f3ff-494e-9e23-e9d9418732e9`) gives the full rigidity
  conjunction in each scope from `CuspidalPairAbsoluteConvergenceStatement`
  and the corresponding completed pole input, `CuspidalPairPoleStatement`
  or `CuspidalPairPoleTCStatement`. It obtains the logarithmic limit and
  all-power trace independence, then derives trace and Euler constituent
  recovery as in JS II 4.1–4.2 and 4.4, pp. 805–807, 809. The exact
  induction proof uses recovery for the arbitrary cuspidal competitor,
  including nonunitary classes. [Landau reduction](../../Langlands/Automorphic/Unramified/CuspidalSpectralRigidityLandauReduction.md), [TC rigidity](../../Langlands/Automorphic/Unramified/CuspidalSpectralRigidityTCStatement.md)
- Task 6822 `a8e36011-2be8-46cc-a440-0da01109d6e6` published
  `cuspidalPairAbsoluteConvergence_of_selfPairContinuation`
  (`37f9ec80-4e6e-46a3-a045-54ebac2da712`). Task 6821
  `1d8cbc81-142d-47eb-9f4d-8b2b13f0fd52` published
  `cuspidalSelfPairContinuation` (`252cfd3f-ba30-42ae-8074-0499eae137eb`),
  which supplies its premise at the same universes. This leaves the
  completed pole input for each scope and the exact rigidity assembly.
  Task 5921 `786d8bc1-6a9b-4fa0-ae6c-89e17489000c` owns the unrestricted
  pole proof and the TC supporting proof under revision 2.
  [Absolute convergence](../../Langlands/Global/Factors/CuspidalPairAbsoluteConvergenceProof.md), [self-pair continuation](../../Langlands/Global/Factors/CuspidalSelfPairContinuationProof.md), [completed poles](../../Langlands/Global/Factors/CuspidalPairPoleStatement.md), [TC completed poles](../../Langlands/Global/Factors/CuspidalPairPoleTCStatement.md)
- `Langlands.Global.HeckeCharacter.cyclicNormKernelCharacter` is a
  published proof, Task 7733 `1649c12b-2d57-4323-9e10-1550a64b3a0f`,
  artifact `667aa852-5152-4d3f-849a-184fd20784ff`. The local unramified
  order and tower restriction are the separate statements in the table.
  [Norm-kernel character proof](../../Langlands/Global/Arithmetic/CyclicNormKernelCharacterProof.md)
- `Langlands.Automorphic.cuspidalArithmeticSpectralTransport` and
  `CuspidalSpectralPresentation.arithmeticComap` are published in
  `d28e00be-50c9-4df8-99a0-121f4a75b754`, Task 7880
  `46944320-f7ea-480c-bc6a-dd6867f8a944`. Task 7970 uses this
  transport to identify the reindexed spectral system for the
  prescribed arithmetic comap. Task 7973 reuses
  `cuspidalIrreducibleAdmissibleFiniteSliceExistence`,
  `CuspidalOperatorRealization.exists_presentation_of_finiteSlice`
  and `CuspidalSpectralUniverseLift` from the existing construction
  program. [Arithmetic spectral transport proof](../../Langlands/Automorphic/CuspidalArithmeticSpectralTransportProof.md)
- Task 7868 `e49b1501-66f5-4b5f-9757-fcc4f1f7fad8` revision 2 owns
  the full ordinary and twisted discrete comparison, including
  proper-Levi terms, Hecke isolation and the analytic step of joint
  strict-rank induction in AC III.4.2(a), (b), (d) and (e).
  The published `CyclicPrimeJointRankInductionStatement` module
  `34c6a785-a82f-4f7b-ae8f-e939011a9cd3` gives both scopes of the
  rank step, the all-ranks result and the reduction of the latter to
  the former. The going-up part yields
  `CyclicPrimeCuspidalBaseChangeExistenceTCStatement`, published in
  `091573f1-2c7c-496a-a564-2fcba9b70368`, for Task 7860's assembly
  of III.4.2(c). Task 7868 retains the proof planning of these
  published interfaces, whose proofs are open. The induction
  applies going up or down only at strictly smaller ranks.
  [Joint rank induction](../../Langlands/Automorphic/Unramified/CyclicPrimeJointRankInductionStatement.md), [TC singleton base change](../../Langlands/Automorphic/Unramified/CyclicPrimeCuspidalBaseChangeExistenceTCStatement.md)
- Task 7868 published `Langlands.BaseChange.FinitePlaceFullMatchingStatement`
  (`e44dae08-e2db-4081-8f35-f1b643bb25ad`) for both directions of full
  finite-place matching in AC I.3.1, p. 20. AC I.4 concerns unramified
  spherical matching. `Langlands.BaseChange.SplitArchimedeanMatchingStatement`
  and `Langlands.BaseChange.NonsplitRealMatchingStatement` share
  publication `e4d435df-ba72-4ae8-99e0-9af4c60162c4`. The former gives
  the split convolution of AC I.5 (5.1)–(5.2), pp. 48–49, which the TC
  comparison uses at complex places. The latter gives AC I.7.3,
  pp. 73–74, for the unrestricted comparison.
  [Finite matching](../../Langlands/BaseChange/FinitePlaceFullMatchingStatement.md), [archimedean matching](../../Langlands/BaseChange/ArchimedeanLocalMatchingStatement.md)
- Task 7868 also published `Langlands.TraceFormula.CyclicSplitCenterMeasureStatement`
  (`7e280fa6-9a8a-4cfc-a9f0-f463374669d9`) and
  `Langlands.TraceFormula.CyclicEqualBlockLeviCountStatement`
  (`14e27fcb-7f3a-4d62-94ce-99590fbb3437`). The compatible measures
  and equal-block Weyl count enter both scopes of the comparison in
  II.(17.7)–(17.8) and the proper-Levi calculation of III.4.2.
  Task 7868 owns the proof planning, remaining interfaces and focused
  proof tasks. [Split-centre measure](../../Langlands/TraceFormula/CyclicSplitCenterMeasureStatement.md), [Weyl weights](../../Langlands/TraceFormula/CyclicDiscreteWeylWeights.md)
- Task 7866 `baaddc1e-26c5-41f7-8ebc-fe5c6e08a21b` owns the
  statement and proof planning for the finite character-twisted trace
  comparison, endoscopic support and spectral detection of CR §§4–7,
  PDF pp. 10–26. Its stabilized distribution contains the cuspidal,
  residual and regular proper-Levi terms. The rank divisibility,
  test space and other supporting candidates were in staging at this
  snapshot. The exact obstruction tasks use this program in the
  unrestricted and totally complex scopes.

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
