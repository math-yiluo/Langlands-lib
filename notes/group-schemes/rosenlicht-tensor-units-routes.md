# Rosenlicht tensor units: sources and a possible finite-dimensional route

Worker 866, 17 November 2026.

This note records a source and API investigation for the affine prerequisite of
Milne's product-units theorem. It supplies no Lean proof of that prerequisite.
The possible route below is an internal mathematical argument awaiting
formalization and independent review.

## Exact prerequisite and ownership

For an algebraically closed field `k`, finitely generated commutative
`k`-domains `A` and `B`, and a unit `z` of the actual algebra tensor product
`A ⊗[k] B`, the desired conclusion is

```text
there are a ∈ Aˣ and b ∈ Bˣ with z = a ⊗ b.
```

The universes of `k`, `A` and `B` are independent. There are no chosen rational
points, normality assumptions, or supplied compactifications in the statement.
Task 7474 (`15f9a031-4b39-42ae-b921-5a37925bead1`) owns statement and exact-proof
publication. Task 6784 (`ee008e9d-0470-4548-87d4-ffeb51863581`) owns the passage
from affine tensor units to the scheme-level
`Langlands.GroupScheme.UnitsProductDecompositionStatement`. The tensor
prerequisite must not depend on that scheme-level result.

## Read primary sources

David B. Jaffe, *Functorial structure of units in a tensor product* (1994),
[arXiv version 1](https://arxiv.org/abs/alg-geom/9410010v1), Lemma 4.1, pp.11–12,
states tensor-unit splitting for reduced connected algebras over an
algebraically closed field. Its proof, credited to Guralnick, enlarges the
field to be uncountable. It uses finite generation of units modulo constants,
then covers the maximal-point space by countably many closed loci of fixed
normalized specializations. An irreducible component lies in one locus;
connectedness identifies the values across components. In the finite-type
domain case required here, this still needs both a units-modulo-scalars theorem
and the uncountable closed-cover argument. The paper is registered as
`jaffe-1994-functorial-units-tensor`.

Brian Conrad, *Units on product varieties*,
[author-hosted note](https://math.stanford.edu/~conrad/papers/unitthm.pdf),
Theorem 1.1 and Sections 2–3, pp.1–3, gives the product-units result for
geometrically connected geometrically reduced schemes locally of finite type
with rational points. The proof reduces to normal projective compactifications,
records orders on boundary divisors, and proves compatibility of these orders
with generic specialization in Lemma 3.1. It therefore does not remove the
compactification and divisor obligations. Section 4, pp.3–4, removes the rational
point hypotheses by Galois descent and Hilbert 90. All four pages were read.
The note is registered as `conrad-units-product-varieties`.

These sources explain two valid proof routes. Neither is an existing
formalized tensor-unit theorem.

## Possible route through bounded inverse pairs

The following is internal reasoning, not a proof attributed to either source.
It replaces a theorem about the entire unit group by a finite-dimensional
finiteness lemma.

Let `B` be a `k`-domain, let `ε : B →ₐ[k] k` be an algebra map, and let `V,W`
be finite-dimensional `k`-subspaces of `B`. Consider

```text
S = { (v,w) ∈ V × W : vw = 1 and ε(v) = ε(w) = 1 }.
```

A proposed first lemma is that `S` is finite. A projective argument for it is:

1. Put `E = V ⊗[k] W`, and let `m : E →ₗ[k] B` be multiplication.
   In `P(E)`, impose the rank-one equations and the linear equations
   `m(t) ∈ k·1`. These define a closed projective subscheme `Z`.
   Only the finite-dimensional span of `1` and the products `VW` is needed
   to express the multiplication equations.
2. Let `L = ε ∘ m`, a linear form on `E`. A nonzero decomposable `k`-point
   `t = v ⊗ w` on `Z` has `m(t) = c·1`. The domain property gives `c ≠ 0`,
   so `L(t) = c ≠ 0`.
3. Thus the closed subscheme `Z ∩ V(L)` has no `k`-point. Since it is of
   finite type over an algebraically closed field, it is empty. This
   finite-type argument is necessary: checking only rational points is
   not by itself a general scheme-theoretic containment proof.
4. Consequently `Z` is closed in the affine chart `D(L)`. Its structure
   morphism is both proper and affine, hence finite. It has finitely many
   `k`-points.
5. A normalized pair in `S` determines a point `[v ⊗ w]` of `Z`.
   Equality of these projective tensors gives proportional nonzero factors.
   Applying `ε` to both normalized factors forces the proportionality
   constants to be one. Hence this map from `S` is injective.

The tensor-unit conclusion would then follow by specialization, without
uncountability or finite generation of the entire unit group:

1. Choose `ε : B →ₐ[k] k` using finite type and the weak Nullstellensatz.
   Evaluate `z` along `ε` to obtain a unit `a ∈ Aˣ`.
2. Normalize `z` by multiplication with `(a⁻¹ ⊗ 1)`. Both this tensor and
   its inverse evaluate to `1` along `ε`. Choose finite-dimensional
   subspaces `V,W ⊆ B` containing their respective coefficients.
3. Every algebra map `x : A →ₐ[k] k` gives a pair in the finite set `S`.
   For a fixed pair, the locus of such `x` giving that pair is cut out by
   finitely many coefficient equations, hence is closed.
4. These finitely many loci cover the rational points of `Spec A`.
   Density of rational points and irreducibility imply that one locus
   is all of `Spec A`. Reducedness then detects equality of the
   normalized tensor with `1 ⊗ b`, for a fixed unit `b ∈ Bˣ`.
   Undoing normalization gives `z = a ⊗ b`.

This outlines the missing mathematics more locally, but leaves substantial
formal work: the rank-one projective locus, its rational-point description,
the affine-chart factorization, finite rational points, and the specialization
and tensor-equality lemmas. It is a proposed alternative, not a claim that the
available APIs already discharge those obligations.

## API inventory and search limits

The audit used Library base `fcb85a7ef43356fec01e6ccf1605f08568c08cb0`
and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

| Available source | Relevant API or scope |
| --- | --- |
| `Mathlib/RingTheory/Nullstellensatz.lean` | `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal` and `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` provide polynomial rational-point and radical statements. |
| `Mathlib/RingTheory/NoetherNormalization.lean` | `exists_integral_inj_algHom_of_fg` and `exists_finite_inj_algHom_of_fg`; neither is a units theorem. |
| `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean` | Properness of `Proj.toSpecZero` for the finite-type graded algebra. |
| `Langlands/AlgebraicGeometry/ProjectiveSpace/Structure.lean` | `projectiveSpaceToSpec_isProper` gives properness of the actual projective-space model. |
| `Langlands/AlgebraicGeometry/ProjectiveSpace/CoordinateEmbedding.lean` | `Langlands.AlgebraicGeometry.ProjectiveSpace.isClosedImmersion_map_of_surjective` supports closed embeddings from maps surjective in every degree. |
| `Langlands/AlgebraicGeometry/ProjectiveSpace/RationalPointZeros.lean` | `HasCoordinates`, coordinate nonvanishing, and rational-point equations for the Library projective-space model. |
| `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean` | `AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom`. |
| `Langlands/AlgebraicGeometry/ProperConnectedAffineConstancy.lean` | Constancy of affine-valued maps from proper connected reduced schemes over algebraically closed fields; it assumes properness and does not apply directly to `Spec A`. |

Focused name and text searches in Mathlib's ring theory and algebraic geometry
and the Library's algebra and algebraic geometry directories found no direct
tensor-unit splitting theorem, finite-generation theorem for units modulo
scalars, or uncountable closed-cover theorem. This records those searches;
it is not an exhaustive declaration audit. No Segre construction was found in
the searched projective-space and projective-bundle directories.
