# Parity correction and determinant untwisting in Harris Proposition 4.8

Task 7218 `8a1e00f3-5223-4c5a-9994-f8f08331ceda` decomposes
four published targets. The parent induction in Task 6413
`bca10e59-d4e2-40a4-be9b-5d70eaa1acd2` uses
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
`IsAlgebraicAfterTwist m ν`. Task
`a6de2478-e39e-494e-9787-4f2cf8dffd07` published the exact
half-weight proof. Harris's p. 195 normalization fixes the required
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
The arbitrary-character operator and spectral constructions belong
to Task `6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`. The existing exact
existence theorem `cuspidalDeterminantMultiple` belongs to Task
`3769037c-895e-48df-bd60-2326fcd3195c` under the spectral program
`34b81620-20d7-4059-9b08-6bedd1c1c029`. [Henniart 2000, §2.2, p. 444](https://doi.org/10.1007/s002229900033), [operator twist](../../Langlands/Automorphic/HeckeTwist/OperatorTwist.md), [spectral twist](../../Langlands/Automorphic/HeckeTwist/CuspidalSpectralTwist.md)

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

## Proof owners

Each row names the exact target and the owner of its proof. The
conditional reductions use their listed premises as hypotheses. The
four final proofs apply the reductions to the corresponding proved
inputs. Task 7216 `22c6a336-836c-47dc-bc09-667768393b20` owns the
auxiliary rank-one theorem used in `Proposition48AuxiliaryPreparationStatement`.

| Lean proposition | Proof task | Task ID |
| --- | --- | --- |
| `Langlands.Global.Harris.NormTwistInfinityStatement` | Task 7976 | `0e02d45c-f040-4f5c-94d4-e30523e7791e` |
| `Langlands.Global.Harris.CMNormConjugationStatement` | Task 7979 | `cf4011eb-a860-47ba-ba5c-9a22029821ba` |
| `Langlands.Global.Harris.Proposition48PlaceNormTwistStatement` | Task 7980 | `f941d28c-0f0b-455b-b4f0-b4f188daaf78` |
| `Langlands.Global.Harris.GeneralPositionAmbientTwistStatement` | Task 7984 | `399b0ff8-364f-43e0-86a2-2b6dc6b1e545` |
| `Langlands.Automorphic.HeckeDeterminantTwistWeakInductionStatement` | Task 7987 | `24e7b7ec-1742-4785-a2ed-22f26c24654c` |
| `Langlands.Automorphic.HeckeDeterminantTwistConjugateSelfDualStatement` | Task 7992 | `31a1744b-6943-42e8-9162-281e0ce7ca69` |
| `Langlands.Automorphic.HeckeDeterminantTwistSupercuspidalStatement` | Task 7994 | `f1527661-b13e-485a-8540-dd83e0902996` |
| `Langlands.Global.Harris.Proposition48AuxiliaryParityNormalizationReductionStatement` | Task 7998 | `6e0238d9-396c-4663-b69d-637cc3410a75` |
| `Langlands.Global.Harris.Proposition48ParityNormalizationReductionStatement` | Task 8002 | `3b14cebe-07fc-439d-8fcd-dc1b5c2e2efc` |
| `Langlands.Global.Harris.Proposition48AuxiliaryParityUntwistReductionStatement` | Task 7999 | `9809445d-8bfc-4b98-9a5d-d1ec1536ea3e` |
| `Langlands.Global.Harris.Proposition48ParityUntwistReductionStatement` | Task 8004 | `eeea4949-8944-491b-82b2-5f1122cd694b` |
| `Langlands.Global.Harris.Proposition48AuxiliaryParityNormalizationStatement` | Task 8008 | `43773cdb-ef60-41ae-af67-d0af2841ac5b` |
| `Langlands.Global.Harris.Proposition48AuxiliaryParityUntwistStatement` | Task 8009 | `85c6a682-6a41-4de3-a549-d368a770d640` |
| `Langlands.Global.Harris.Proposition48ParityNormalizationStatement` | Task 8010 | `e3d5a2b0-045c-4131-81bc-0b7f1607ed57` |
| `Langlands.Global.Harris.Proposition48ParityUntwistStatement` | Task 8011 | `ad904027-ae18-4d99-9955-c40fc259bc62` |
| `Langlands.Global.Harris.Proposition48ParityTransportStatement` | Task 8013 | `b7b4cc85-a4ba-4a8c-bcac-08cca3b0b4d1` |
| `Langlands.Global.Harris.Proposition48AuxiliaryPreparationStatement` | Task 8012 | `fa892b08-e57f-4263-97de-8919119cb536` |
