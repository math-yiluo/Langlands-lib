# Valued-field amalgamation: tensor sources and proof route

Author: Worker 74. This note records an original-source route to a missing
analytic prerequisite of the full presented-affinoid domain spectrum
embedding. It supplies source correspondence and a mathematical derivation;
it supplies no Lean proof of tensor norm properties, general Banach spectrum
nonemptiness, field amalgamation, or `Domain.SpectrumEmbeddingStatement`.

## Sources and reading

- Itaï Ben Yaacov, *Tensor products of valued fields*, retained author-hosted
  four-page version:
  `literature/Ben Yaacov, Tensor products of valued fields (2015).pdf`,
  source `ben-yaacov-2015-tensor-products-valued-fields`,
  SHA256 `9fe54c994f66a41132e4593626c05f930f884276ff0a1ee8786fbdd2a9f280a0`.
  [Author's original PDF](https://math.univ-lyon1.fr/~begnac/articles/ValuedTensorProduct.pdf).
  All four pages were read; the formulas in Definition 6 and Lemma 7 on
  page 2 were also checked in the rendered original.
- V. G. Berkovich, *Spectral theory and analytic geometry over
  non-Archimedean fields* (1990):
  `literature/Berkovich 1990 Spectral theory and analytic geometry over non-Archimedean fields.pdf`,
  source `provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
  SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
  The relevant passages are Chapter 1, printed pages 11–14 / one-based
  PDF pages 25–28, including Theorem 1.2.1 and Remarks 1.2.2(i).
- L. Gruson and M. van der Put, *Banach spaces* (1974):
  `literature/Gruson and van der Put, Banach spaces (1974).pdf`,
  source `gruson-van-der-put-1974-banach-spaces`,
  SHA256 `309eaf4469b0134ef0bce38eb02edccfe7e024169ebef2d8cb685ddcc51b458e`.
  [Original PDF](https://www.numdam.org/item/MSMF_1974__39-40__55_0.pdf).
  The global assumptions on printed page 56 and Lemma 5.2 on printed
  pages 76–78 / PDF pages 23–25 were read; the page 77 formulas were
  checked in the rendered original.

No corresponding errata file was present in the inspected Library
`b4b4160d118213b51ef28eb814f1828ac3902ada`.

## The tensor estimate includes trivial valuations

In Ben Yaacov's Definition 6, let F be any real-valued non-Archimedean
valued field and let V and W be seminormed F-vector spaces. For an algebraic
tensor t, set

\[
 p(t)=\inf_{t=\sum_i v_i\otimes w_i}\max_i\|v_i\|\|w_i\|.
\]

Lemma 7(i) proves that p is a seminorm, and that it is submultiplicative
when V and W are F-algebras with submultiplicative seminorms.
Lemma 7(ii) reduces the infimum to presentations of minimal tensor rank.
Its proof eliminates a linear dependence without increasing the displayed
maximum. Lemma 7(iii) then gives

\[
 p(v\otimes w)=\|v\|\|w\|.
\]

These statements assume neither completeness nor algebraic closure of F,
and do not exclude its trivial valuation. This scope follows from
Definition 6 and the actual hypotheses of Lemma 7. The stronger Theorem 9
assumes an algebraically closed base and proves multiplicativity of p on
the whole tensor algebra; its separate trivial-valuation argument on
page 3 retains that algebraic-closure assumption. That theorem cannot be
applied directly to an arbitrary completed residue field.

Gruson–van der Put's Lemma 5.2 also supplies a tensor norm and the pure
tensor identity, including an elementary proof using finite approximately
orthogonal bases. Their global setup assumes a nontrivial valuation.
Ben Yaacov's Lemma 7 is therefore the more directly applicable source for
the pure tensor identity in the unrestricted present task.

## Derived common-field route

Let F be a complete real-valued ultrametric field, and let E and G be
complete real-valued ultrametric extensions with specified isometric
embeddings of F. Apply Lemma 7 to E and G over F.

1. Give \(E\otimes_F G\) the seminorm p above, pass to its separated
   quotient, and complete it to a commutative Banach F-algebra T.
   Submultiplicativity permits multiplication to descend and extend.
   The pure tensor identity gives \(p(1\otimes1)=1\), so T is nonzero.
   The factor maps \(e\mapsto e\otimes1\) and \(g\mapsto1\otimes g\)
   preserve the original norms and agree on F.
2. Berkovich's Theorem 1.2.1 supplies a bounded multiplicative seminorm
   q on T. Its hypotheses concern a commutative Banach ring with
   normalized unit; they impose no nontrivial valuation on F.
   The power argument on printed page 12 makes q contractive.
3. For nonzero e in E, contractivity on the two inverse elements gives
   \(q(e)\leq\|e\|\) and \(q(e^{-1})\leq\|e\|^{-1}\).
   Their q-values multiply to one, forcing \(q(e)=\|e\|\).
   The same argument applies to G, and zero is immediate.
4. Remarks 1.2.2(i) construct the completed residue field H(q) of T.
   The composites from E and G into H(q) preserve norms, hence are
   isometric field embeddings agreeing on F. The ultrametric norm on T
   bounds the q-values of integers by one, so the induced field valuation
   is non-Archimedean. Its completion is a complete ultrametric field.

This route is a derivation combining the two sources. It does not
attribute arbitrary-base multiplicativity of p to Ben Yaacov, or an
explicit amalgamation theorem to Berkovich. It needs only the pure
tensor identity and submultiplicativity before choosing q.

## Application and remaining formalization

For compatible spectrum points x of B and y of C above a common point z
of A, the intended F, E and G are H(z), H(x) and H(y). The residue-field
maps must be the maps induced by the given bounded maps from A.
Their evaluation squares make the resulting realizations of B and C
agree on A and realize exactly x and y.

The focused helper
`Langlands.Analytic.BanachSpectrum.completedResidueComap`, in
`Langlands.Geometry.Analytic.Spectrum.ResidueField.Lift`, constructs
those isometric residue-field maps. At this note's preparation it had
passed machine validation and independent semantic review as candidate
`04290b67-829b-45ad-b225-2c235122c6b6`, with publication pending.
This helper alone supplies no common field.

The outstanding Lean work includes the ultrametric projective tensor
seminorm and its pure tensor identity, its separated Banach-algebra
completion and factor maps, general Banach spectrum nonemptiness, and
the common-field and compatible-point assembly. The existing
`Langlands.Geometry.Analytic.SpectrumNonemptyProof` treats strict presented
affinoids and does not supply nonemptiness for this arbitrary T.
The implementation must also check all scalar structures and the
required full universe u. Restricting the valuation, radii, or universe
would not discharge the domain spectrum target. Cases with no spectrum
points need no common-field construction.
