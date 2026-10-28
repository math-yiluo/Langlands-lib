# Interior elliptic analytic regularity: the Morrey–Nirenberg route

Worker 94 read the supplied complete original of C. B. Morrey Jr. and
L. Nirenberg, *On the analyticity of the solutions of linear elliptic
systems of partial differential equations*, Communications on Pure and
Applied Mathematics 10 (1957), 271–290, on 28 October 2026. The registered
source is `provided-17e51270c6d50eab8ff7b4142058b4ec69474b21e75225ec9952a95784e8229f`,
retained as `literature/Morrey-Nirenberg - On the analyticity of the solutions of linear elliptic systems of partial differential equations (1957).pdf`,
SHA256 `61c74249e27625fd25cb0a33d3c77d90ab6b5306fc9bccddc7a6d5314229f915`.
The original has 20 pages; one-based PDF page 1 is printed page 271.
The [publisher's record](https://onlinelibrary.wiley.com/doi/abs/10.1002/cpa.3160100204)
identifies DOI `10.1002/cpa.3160100204`.

This note maps an outstanding proof dependency. It proves no elliptic
estimate, analytic regularity, joint-finite analyticity or automorphic
differential growth. It supplements the
[differential-growth source map](differential-growth-source-map.md).

## The relevant scope

The introduction and section 1, printed pages 271–275 / PDF pages 1–5,
distinguish interior analyticity for general elliptic systems from the
strong ellipticity and boundary hypotheses used for the paper's boundary
results. The present automorphic application needs interior analyticity
of an already smooth complex-valued scalar function on an open real
matrix domain. No boundary condition, distributional regularity theorem
or boundary analyticity theorem is needed for that application.

Section 5, printed pages 287–290 / PDF pages 17–20, addresses the interior
problem for general analytic elliptic systems. The operators have complex
analytic coefficients. Ellipticity is expressed by nonvanishing of the
highest-order symbol determinant on nonzero real covectors, with the
orders assigned as in section 1. Locally the argument works on a ball
with a uniform positive homogeneous lower bound for that determinant,
as in (5.2). For the single scalar equation, the determinant is just the
scalar highest-order symbol. This is the source scope needed after
identifying a genuine Cartan polynomial action with an actual elliptic
differential operator. The scalar application need not introduce the
paper's full mixed-order systems first.

## Estimates and their order

Section 5 first treats the homogeneous constant-coefficient system.
Lemma 5.1, printed page 288 / PDF page 18, bounds the required top
L2 derivative norm by the corresponding norm of the equation's right
side, for a smooth function vanishing near the ball's boundary. Its proof
uses the Fourier transform, inversion of the symbol matrix by cofactors,
the homogeneous ellipticity bound and Parseval's identity. In the scalar
case, this inversion reduces to division by the nonzero scalar symbol.
The normalization of the Fourier transform and the factor of `i` in the
symbol substitution must match the chosen formal Fourier convention.

Lemma 5.2, printed page 289 / PDF page 19, applies the constant-coefficient
estimate after multiplying by a smooth cutoff. The estimate on a smaller
ball includes the equation on a larger ball and lower derivatives of the
function, with negative powers of the gap between the radii. The argument
is the interior version of the cutoff calculation in Lemma 3.2, printed
pages 280–281 / PDF pages 10–11. Lemma 5.3 applies this estimate to all
derivatives with a radius gap depending on the derivative order, giving
an inequality for factorially normalized weighted L2 seminorms.

The variable-coefficient argument freezes the top coefficients at the
center of the ball. The difference between the frozen and actual
operators is written as analytic coefficient tensors multiplying
appropriate derivatives. Formula (5.10), printed page 289 / PDF page 19,
uses local factorial derivative bounds for these tensors; the top-order
difference vanishes at the center and is bounded by a constant times the
distance to the center. Shrinking the ball absorbs that top-order term.
Lemma 5.4, printed page 290 / PDF page 20, bounds the next normalized
seminorm by preceding ones. The induction modeled on section 4 yields
(5.5), an exponential bound in derivative order for these normalized
seminorms, equivalently a factorial bound for the unnormalized derivatives.
Section 5 omits some proofs as parallel to the earlier sections; those
calculations remain part of any Lean implementation.

Lemma 2.3 and its corollary, printed pages 276–277 / PDF pages 6–7,
turn the local factorial L2 bounds into analyticity. A local Sobolev
inequality from Lemma 2.2 first bounds pointwise derivatives using finitely
many higher L2 derivatives. The resulting factorial pointwise estimates
imply convergence of the Taylor expansion. The source states the same
argument for full balls, which is the interior case needed here. Merely
having smoothness or bounded derivatives of each fixed order does not
supply the required common factorial estimate.

## Formalization boundaries

A suitable development separates these obligations:

1. Actual finite-order scalar differential coefficients, action and
   highest-order symbol on a finite-dimensional real domain, with complex
   values and explicit coefficient analyticity.
2. The constant-coefficient Fourier L2 estimate.
3. Cutoff and local interior estimates, followed by the frozen-coefficient
   factorial induction.
4. Local Sobolev and factorial-to-analytic implications.
5. The concrete Cartan-polynomial coefficient expansion and its
   highest-order symbol, with transport to the original matrix norm and
   topology.

The current dependent Cartan constructions supply concrete second-order
expressions and coefficient positivity. A separate checked ambient
realization draft identifies their iterates and polynomial coefficient
sums with the genuine enveloping action on units. These are unreviewed
prerequisite developments; they do not identify the highest-order symbol
of every iterate, supply the estimates above or prove analytic regularity.
The published original alone does not fill these Lean obligations.

The local scalar route retains the actual archimedean matrix space and
norm. A coordinate presentation in a fixed finite basis needs an explicit
continuous linear transport, rather than a silent replacement of the
matrix norm. Dimension zero can be handled separately before an
analytic-regularity theorem that presupposes a positive-dimensional
Euclidean domain. No positive-rank restriction may be added to the final
number-field statement.
