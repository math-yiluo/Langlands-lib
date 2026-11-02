# Getz–Hahn Chapter 9: cuspidal proof dependencies and source boundaries

This note records the source route for the cuspidal part of the general
automorphic library, task `34b81620-20d7-4059-9b08-6bedd1c1c029`.
It supplements the [program coverage ledger](global-program-coverage.md).
It is a reading and dependency note, not a proof of closedness, trace class,
rapid decay, or spectral existence.

## Sources and reading extent

The original is Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), registered as `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
Printed pp. 239–267 were directly read, and pp. 263–265 were also visually
checked against rendered pages. Chapter 9 printed pages correspond to
one-based PDF pages twelve higher. The raw height definition on printed
p. 161 and Exercises 6.1–6.6 on p. 180 were directly read at PDF pp. 175 and
194; the offset is not constant throughout the book.

The complete five-page October 2026 author errata was read. Its registered
source is `getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.
The retained file is *Getz–Hahn — Errata for An Introduction to Automorphic
Representations (October 2026).pdf* in the project literature collection.
The [author's book page](https://sites.duke.edu/jgetz/graduate-text/) links
to the [checked errata](https://sites.duke.edu/jgetz/files/2026/10/Errata-3.pdf).
The Chapter 9 entries are on errata pp. 2–3.

GH 9.7.1 cites MW95 I.2.12 for the number-field rapid decay of algebraic
cuspidal automorphic forms. That original passage has **not** been read for
this note. Its result remains an original-source and proof obligation;
GH's citation is not a substitute for either.

## Dependency map

All quotient notation below retains the split-centre convention
`[G] = A_G G(F) \ G(A_F)`. The eventual library must supply the actual
quotient, quotient measure and convolution action.

| Source passage | Required content | Boundary retained |
| --- | --- | --- |
| Definition 9.1.1, (9.3), pp. 240–241; Exercises 9.1–9.5, p. 267 | Hilbert–Schmidt and trace-class operators, basis independence, composition and compactness, and square-integrable kernels | These are infinite-dimensional operator theorems, separate from finite-dimensional group-height norms. |
| Lemma 9.2.1 and Proposition 9.2.3, pp. 242–245 | Closed cuspidal Hilbert subspace; passage between almost-everywhere periods and classical periods for appropriate vectors | The argument uses actual period/Poincaré vectors and smoothing; it does not assert boundedness of every unsmoothed constant-term operator on the full ambient `L²`. |
| Lemma 9.3.1 and Corollary 9.3.2, p. 247 | Compact convolution approximate identities give a Hilbert sum of irreducibles with finite multiplicities | Trace class implies Hilbert–Schmidt and then compactness; a supplied direct-sum presentation is not an existence proof. |
| Lemma 9.3.3, pp. 247–248 | Uniform evaluation estimates, a square-integrable kernel and convolution factorization give trace class | Use estimates for all test functions and justify kernel measurability, as explained below. |
| Lemmas 9.4.1–9.4.6 and Proposition 9.4.7, pp. 249–259 | Well-defined Iwasawa components, vector Fourier estimates, lattice summability and the basic cusp estimate | Relative-root, unipotent, Fourier, convergence and reduction-theoretic inputs remain actual prerequisites. |
| Definition 9.6.1 and Theorem 9.6.4, pp. 263–264 | Rootwise decay on every Siegel set; rapid decay of the smooth representative `R(f)φ` | Preserve the Siegel-set definition; the unrestricted raw-height wording in 9.6.2 needs separate treatment. |
| Corollary 9.6.5, p. 264 | Rapid decay of finite-level, archimedean smooth Hilbert cusp vectors | This is the stated smooth-vector notion, not a statement about arbitrary representatives of an `L²` class. |
| Theorem 9.7.1, p. 264 | Rapid decay of algebraic cusp forms over number fields | MW95 I.2.12 must still be read and implemented. |
| Lemma 9.7.2 and Theorem 9.7.3, pp. 264–267 | Recovery by smoothing, dense algebraic cusp forms, equality of isotypic finite-vector spaces and multiplicities | Requires admissibility, finite-level and infinitesimal-character finiteness, growth, and actual comparison maps. |

The number-field estimate in §9.4 uses reduction to `Q` by restriction of
scalars. The exponential map from the nilpotent Lie algebra to the unipotent
group is used as a scheme isomorphism; it is not a group homomorphism.
The Fourier argument requires vector Fourier theory, compact-parameter
Schwartz bounds, finite-level support control and lower bounds on the
relevant rational lattices. The BCH argument uses an ideal corresponding to
a maximal-parabolic unipotent radical. Vanishing of degenerate terms uses
the actual cusp periods. Interchanging integrals and summing frequencies
requires convergence proofs. Equation (9.38), p. 259, supplies summability
for sufficiently large decay exponent, followed by Hölder's inequality and
the change of variables in the Haar measure.

## Operator formulas and the first formal target

GH works with separable Hilbert spaces. Its modulus convention is the
positive **left** modulus `sqrt(A A*)`; it must not silently be replaced by
`sqrt(A* A)`. For trace, Mathlib's convention that the inner product is
linear in its second argument gives the complex diagonal
`inner ℂ (b i) (A (b i))`.

As checked against Library base `0ebc0efd383ff160084af3b33ab2b7806f7a1dde`
on 2 November 2026, Worker 116 has staged the following focused units:

| Lean module and declaration | Exact scope | Submission status at this check |
| --- | --- | --- |
| `Langlands.Analysis.OperatorIdeals`: `IsHilbertSchmidt`, `leftModulus`, `IsTraceClass`, `hilbertSchmidtNormIn`, `traceNormIn`, `traceIn` in namespace `Langlands.Analysis.OperatorIdeals` | Actual bounded operators, existential Hilbert-basis summability, CFC left square root, and explicitly basis-indexed sums | Candidate `8283e313-e66e-48a7-9b7a-117328293c44`; machine validation passed, independent semantic review and publication pending. |
| `Langlands.Analysis.HilbertSchmidtBasisStatement`: `Langlands.Analysis.OperatorIdeals.HilbertSchmidtBasisIndependenceStatement` | Any two domain Hilbert bases give equivalent squared-image summability and, when summable, equal real sums | Candidate `4a7c53eb-5adb-4834-8c28-3c8e658221ec`; development compilation, proposition inspection and official machine validation passed, independent semantic review and publication pending. |

Neither row is counted here as an accepted-public theorem. The second
module imports Mathlib directly and states the prerequisite in basis sums.
Its extension from separable endomorphisms to arbitrary-index rectangular
operators is explicitly derived content. After the statement is published,
its proof belongs in an exact-target proof child. Trace independence,
absolute convergence of the trace diagonal, ideal laws, Hilbert–Schmidt
composition into trace class, and compactness remain separate obligations.

The pinned Mathlib module
`Mathlib.Analysis.InnerProductSpace.Spectrum` already provides the compact
self-adjoint spectral inputs, including
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`,
`ContinuousLinearMap.finite_dimensional_eigenspace` for nonzero eigenvalues,
and `ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero`.
These were located in the supplied sources. They are reusable inputs to a
representation decomposition proof; no new duplicate spectral-theorem
prerequisite is needed. One still has to implement invariant restrictions,
orthogonal complements, a maximal orthogonal family and the multiplicity
argument. A route using self-adjoint compact convolution approximations
must construct those approximations.

## Quantifiers and measurable kernels in Lemma 9.3.3

For a finite-volume quotient and a closed invariant subspace `V`, use the
simultaneous hypothesis that for **every** test function `f` there is a
constant `C_f` such that

`‖R(f)φ‖∞ ≤ C_f ‖φ‖₂` for every `φ ∈ V`.

The printed lemma is phrased for a given `f`, but its last proof step
factors `f` into finite sums of `f₁ * f₂` and needs Hilbert–Schmidt estimates
for those factors as well. The simultaneous hypothesis is a strengthened
sufficient criterion matching the intended application. This note does
not assert that the literal single-function wording has been repaired or
proved.

Pointwise Riesz representation supplies an `L²` vector for each evaluation
of a smoothed function. It does not by itself supply a jointly measurable
kernel on the product quotient. An implementation must construct the
kernel or a suitable measurable realization, prove its square
integrability, and identify the induced operator. Raw point evaluation of
an arbitrary `L²` equivalence class is not the evaluation functional in
this argument. After the Hilbert–Schmidt result for each factor, the
Dixmier–Malliavin factorization and the operator composition theorem give
trace class.

Exercise 9.4 also asserts separability of `L²(Y, μ)` from σ-finiteness
alone. That implication must not be imported as an unrestricted theorem.
For example, the probability product of uncountably many equiprobable
spaces `{-1, 1}` has an uncountable orthonormal family of coordinate functions:
distinct coordinates have zero inner product by independence and each
has norm one. Thus this finite-measure example has nonseparable `L²`.
This is a derived observation, not an author erratum. Either establish the
additional measurable-space hypotheses for the actual adelic quotient,
or prove the kernel result without assuming separability.

## Rapid decay and representative choice

Definition 9.6.1 quantifies over every Siegel set of (9.23), every real
`r > 1`, and every simple relative root `α`. Its positive constant can
depend on the Siegel set and `r`; the bound is
`|φ(x)| ≤ c α(s_x)^(-r)` for points in that set. Lemma 9.4.1 is needed
to make the component `s_x` independent of the Iwasawa decomposition.

Lemma 9.6.2, as printed, quantifies the raw-height estimate
`|φ(x)| ≤ c ‖x‖^(-r)` over **all** `x ∈ G(A_F)^1`.
The height in (6.7)–(6.8), p. 161, is a product of local entry maxima of
a fixed faithful inverse-augmented matrix embedding. It is not a quotient
height.

There is a concrete representative obstruction. For `SL₂/Q`, take
the rational matrices `γ_m = [[1,m],[0,1]]` with positive integers `m`,
and use the embedding obtained from the standard faithful representation
as in (6.3). Each finite-place factor of their height is one, and the real
factor grows with `m`. Their class in `[G]` is the identity class, so
`φ(γ_m) = φ(1)`. The printed all-representative estimate would force
`φ(1) = 0`. This calculation explains why the unrestricted raw-height
wording cannot simply be used as the formal rapid-decay interface.
It is not a formal counterexample consisting of a constructed nonzero
rapidly decreasing function, and no corrected equivalence is proved here.

Keep Definition 9.6.1. A quotient-height or reduced-representative
reformulation is a separate derived statement needing its own proof.
The checked author errata has no 9.6.2 entry. Lemma 9.6.3 cites 9.6.2
in its compact-right-translate argument, so reusing that proof route also
requires addressing the representative issue.

Theorem 9.6.4 concerns the smooth function representing `R(f)φ`.
Corollary 9.6.5 uses one compact open level in the finite adeles and
smoothness for the real group action on that level. Its proof uses
Dixmier–Malliavin to express a vector as a finite sum of smoothed cusp
vectors. Finite level, archimedean smoothness, maximal-compact finiteness
and infinitesimal-character finiteness must retain their distinct roles.

## Author corrections and algebraic/Hilbert comparison

The §9.2 errata corrects the period quotient after (9.9) to
`A_G H(F) \ A_G H(A_F)`. In the later proof of 9.2.6 it also corrects
the character factor to `χ δ_G` and the domain of `h` to the quotient
with `A_G` included. The actual modular convention and conjugates must
be checked in the rendered formulas when implementing the period proof.

The §9.5 errata corrects the claim that `R(f)φ ≠ 0` makes the input
`φ` fixed by `K`. The operator preserves the `K`-fixed cusp space
and maps the entire cusp space into it. Support control applies to
this image. Although the present task's primary scope is number fields,
the function-field argument must retain this corrected direction if reused.

Theorem 9.7.3 supplies several conclusions: dense embedding of algebraic
cusp forms into the Hilbert cusp space, equality of the algebraic and
Hilbert isotypic finite-vector spaces, finite equal multiplicities, an
algebraic direct sum, and a bijection of irreducible isomorphism classes.
The initial embedding uses rapid decay and finite quotient volume.
The converse comparison uses recovery by convolution and the
almost-everywhere-to-classical period passage. In the number-field
algebraic direct-sum argument, one works with a finite collection of
compact types, a finite level and a finite-codimensional ideal of `Z(g)`;
Harish-Chandra finiteness 6.3.4 and moderate growth 4.4.13 then enter.
An abstract Hilbert sum does not establish these comparisons or
construct the algebraic cusp forms.

This Chapter 9 route addresses the cuspidal summand. It supplies neither
an identification of the entire discrete spectrum with cusp forms nor
the continuous-spectrum transform required in the later L2–L3 blocks
of the program.
