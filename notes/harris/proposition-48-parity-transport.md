# Parity correction and determinant untwisting in Harris Proposition 4.8

This note decomposes four statements of the Library. The reduction of
Harris 1998, Proposition 4.8, to named inputs uses
`Proposition48AuxiliaryParityNormalizationStatement` and
`Proposition48AuxiliaryParityUntwistStatement`. The full
`Proposition48ParityNormalizationStatement` and
`Proposition48ParityUntwistStatement` concern the auxiliary and
primary places together. The auxiliary-valid Mackey child supplies
only the auxiliary completion identification. The two-place
reductions use the auxiliary results in that direction. The field and
carrier universes remain independent throughout. [Auxiliary targets](../../Langlands/Global/Arithmetic/HarrisProposition48AuxiliaryInputStatement.md), [two-place targets](../../Langlands/Global/Arithmetic/HarrisProposition48ParityStatement.md)

## Correcting character and arithmetic transport

Set `d = [E' : E]` and `m = (b + (d − 1)) % 2`, where `b` is the
input twist exponent. For equal parities take the trivial Hecke
character. For unequal parities take exponent one at embeddings
of `E` that restrict to a fixed embedding of the given imaginary
quadratic subfield, and zero at those restricting to its conjugate.
This gives a pure weight-one integral infinity type. Apply
`Langlands.Global.cmHalfWeightCharacter` with the empty finite set.
Its actual idele-class character `ν` is conjugate-inverse and has
`IsAlgebraicAfterTwist m ν`. The Library proves the half-weight
statement (`cmHalfWeightCharacter`). Harris's p. 195 normalization fixes the required
parity. His half-integral twist remark on p. 191 concerns fields of
definition. The conjugate-inverse character construction comes from
Harris–Taylor, Proposition VII.2.7 (printed p. 238) and the proof of
Corollary VII.2.8 (pp. 244–245). [Harris 1998, TeX lines 866–875 and 1180–1219](https://arxiv.org/abs/math/9611226), [Harris–Taylor 2001](https://press.princeton.edu/books/paperback/9780691090924/the-geometry-and-cohomology-of-some-simple-shimura-varieties), [half-weight proof](../../Langlands/Global/Arithmetic/CMHalfWeightCharacterProof.md)

The inducing character is multiplied by `ν ∘ N_{E'/E}` using
`Proposition48Problem.correctedCharacter`. At infinity, norm
pullback adds the type pulled back by restriction of embeddings.
In the complex completion coordinates the local norms have degree
one, and a conjugate orientation interchanges the exponents.
The exponent `b + m` is congruent to `d − 1` modulo two, so the
period-two lemma supplies the required normalization. The factors
introduced by `ν` agree on the two components being compared over
a lower archimedean place, as in Harris's Definition 2.3, p. 193.
They are nonzero, so relative regularity survives. For conjugation,
start with `Langlands.Global.HarrisDatum.complexConj_algebraMap`,
transport it to the completions and reindex the determinant norm
products. The resulting equivariance of the idele-class norm preserves
conjugate inversion of the product. [Arithmetic transport](../../Langlands/Global/Arithmetic/HarrisParityArithmeticTransportStatement.md), [Harris 1998, Definition 2.3](https://arxiv.org/abs/math/9611226)

At a compatible finite place, use the actual completion tower and
its field isomorphisms to transport the corrected component. The
finite component formula makes the correction the pullback of the
lower character along the local norm. Norm reciprocity realizes
this as the restriction of a single ambient Weil character at that
place. At the auxiliary place, twist each Mackey constituent by
the appropriate restriction of that ambient character. This keeps
all the irreducibility conditions in the original cyclic tower
of Harris, Definition 4.5 (printed p. 201). Full normalization
uses the same `ν` at the primary place and reassembles the original
place compatibilities, uniqueness and distinctness conditions.
[Finite component and general position](../../Langlands/Global/Arithmetic/HarrisParityLocalTransportStatement.md), [Harris 1998, Proposition 4.8 proof, pp. 201–203](https://arxiv.org/abs/math/9611226)

## Actual determinant untwisting

Choose an actual representative `T` of the corrected cuspidal
class `c` and take `S = T.heckeDeterminantTwist ν⁻¹`. The
multipliers cancel on every adelic group element. The inverse
linear equivalence consequently sends `S` to `T` by multiplication
by `ν(det g)`, giving `OperatorRealization.IsDeterminantMultiple`.
The arbitrary-character operator and spectral constructions are in the
operator-twist and spectral-twist modules linked here; the existence
theorem `cuspidalDeterminantMultiple` is in
`Langlands/Automorphic/CuspidalDeterminantMultipleProof.lean`. [Henniart 2000, §2.2, p. 444](https://doi.org/10.1007/s002229900033), [operator twist](../../Langlands/Automorphic/HeckeTwist/OperatorTwist.md), [spectral twist](../../Langlands/Automorphic/HeckeTwist/CuspidalSpectralTwist.md)

- The actual twisted presentation transports the finite slice and
  local factors, with component equivalences at each finite place.
  Its finite exceptional set is enlarged by the integral tail of
  the twisting character. [Spectral presentation twist](../../Langlands/Automorphic/HeckeTwist/CuspidalSpectralTwist.md)
- Weak induction uses the actual presentation at `T`. At a good
  finite place the twisted Euler polynomial substitutes
  `ν_v⁻¹(π_v) X` for `X`. The norm of any upper
  uniformizer equals the lower uniformizer to the residue-degree
  power modulo integral units, so the inducing product undergoes the
  same substitution. Using `ν⁻¹` cancels the factors from the two norm
  pullbacks. The Euler system of `S` then satisfies the weak induction
  relation for the original character `ξ` of Harris's Definition
  1.3(b), p. 186. [Weak induction twist](../../Langlands/Automorphic/HeckeDeterminantTwistWeakInductionStatement.md)
- Conjugate self-duality is carried by the actual bilinear pairing.
  The conjugate-inverse law for `ν⁻¹` makes the two character values
  cancel on conjugate finite and compact group elements.
  Differentiating their product cancels the Lie shifts. The two
  functional transport directions identify the smooth, compact-finite
  image of the pairing. [Conjugate self-duality and supercuspidality twist](../../Langlands/Automorphic/HeckeDeterminantTwistDualitySupercuspidalStatement.md)
- Supercuspidality uses a presentation at `T` witnessing the auxiliary
  component. The existing local class comparison identifies the
  twisted component with the character twist, realized by
  `Correspondence.supercuspidalTwist` on the supercuspidal class.
  The proof may choose the presentation separately from the weak
  induction witness. [Local class comparison](../../Langlands/Automorphic/AssociatedGammaAutomorphicTwist.md), [supercuspidal class twist](../../Langlands/Correspondence/SupercuspidalOperationRealization.md)

`T` retains the four corrected solution properties. The regular
algebraicity clause belongs to `T`. The realization `S` has weak induction of the
original character, conjugate self-duality, and the auxiliary
supercuspidal component. The full untwist projects the full raw
and corrected data to the auxiliary data and gives the same
conclusion. [Four reductions](../../Langlands/Global/Arithmetic/HarrisProposition48ParityReductionStatement.md)

## Proof status

Each row names the exact target and its status in the Library. The
conditional reductions use their listed premises as hypotheses. The four
final proofs are to apply the reductions to the corresponding proved
inputs. `Proposition48AuxiliaryPreparationStatement` also uses the
auxiliary rank-one theorem.

| Lean proposition | Proof |
| --- | --- |
| `Langlands.Global.Harris.NormTwistInfinityStatement` | proved: `normTwistInfinity` |
| `Langlands.Global.Harris.CMNormConjugationStatement` | proved: `cmNormConjugation` |
| `Langlands.Global.Harris.Proposition48PlaceNormTwistStatement` | proved: `proposition48PlaceNormTwist` |
| `Langlands.Global.Harris.GeneralPositionAmbientTwistStatement` | proved: `generalPositionAmbientTwist` |
| `Langlands.Automorphic.HeckeDeterminantTwistWeakInductionStatement` | proved: `heckeDeterminantTwistWeakInduction` |
| `Langlands.Automorphic.HeckeDeterminantTwistConjugateSelfDualStatement` | proved: `heckeDeterminantTwistConjugateSelfDual` |
| `Langlands.Automorphic.HeckeDeterminantTwistSupercuspidalStatement` | proved: `heckeDeterminantTwistSupercuspidal` |
| `Langlands.Global.Harris.Proposition48AuxiliaryParityNormalizationReductionStatement` | proved: `proposition48AuxiliaryParityNormalizationReduction` |
| `Langlands.Global.Harris.Proposition48ParityNormalizationReductionStatement` | proved: `proposition48ParityNormalizationReduction` |
| `Langlands.Global.Harris.Proposition48AuxiliaryParityUntwistReductionStatement` | proved: `proposition48AuxiliaryParityUntwistReduction` |
| `Langlands.Global.Harris.Proposition48ParityUntwistReductionStatement` | proved: `proposition48ParityUntwistReduction` |
| `Langlands.Global.Harris.Proposition48AuxiliaryParityNormalizationStatement` | no theorem; it follows from proved results: `proposition48AuxiliaryParityNormalizationReduction` with `normTwistInfinity`, `cmNormConjugation`, `proposition48PlaceNormTwist` and `generalPositionAmbientTwist` |
| `Langlands.Global.Harris.Proposition48AuxiliaryParityUntwistStatement` | no theorem; it follows from proved results: `proposition48AuxiliaryParityUntwistReduction` with `heckeDeterminantTwistWeakInduction`, `heckeDeterminantTwistConjugateSelfDual` and `heckeDeterminantTwistSupercuspidal` |
| `Langlands.Global.Harris.Proposition48ParityNormalizationStatement` | no theorem; it follows from proved results: `proposition48ParityNormalizationReduction` with the auxiliary normalization above and `proposition48PlaceNormTwist` |
| `Langlands.Global.Harris.Proposition48ParityUntwistStatement` | no theorem; it follows from proved results: `proposition48ParityUntwistReduction` with the auxiliary untwist above |
| `Langlands.Global.Harris.Proposition48ParityTransportStatement` | no theorem; it is the conjunction of the two statements above, which follow from proved results |
| `Langlands.Global.Harris.Proposition48AuxiliaryPreparationStatement` | no theorem; it is the conjunction of `Proposition48AuxiliaryRankOneStatement` (proved: `proposition48AuxiliaryRankOne`) and the two auxiliary statements above, which follow from proved results |
