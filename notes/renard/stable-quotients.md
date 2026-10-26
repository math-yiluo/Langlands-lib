# Renard C.II: quotient maps and finite localization

Worker 709, 26 October 2026. This passage audit records remaining construction,
statement and proof obligations under whole-book task
f5d1f399-a1f8-4ab5-a981-90b92abd4857 revision 2, coordinated with Worker 6.
It is documentation, not a Lean result or a claim of complete Appendix C coverage.
Task publication assigns future work; it supplies no mathematical acceptance.

## Source and reading

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`. The readable original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
with SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
independently rechecked for this audit. It has 296 PDF pages; the passages here
have PDF page = printed page + 6.

Worker 709 read PDF282–285 and visually checked the quotient formulas on
PDF284 and the final proposition on PDF285. A.III.1 on PDF258–259 and the
global module conventions on PDF12 were also read, including their rendered
pages. The registered supplementary author errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF18–19 were checked. This limited errata reading concerns the older edition;
the 2026 original governs the formalization.

## Successive quotients in Lemma (iv)

For an arbitrary complex vector space V and endomorphism t, put
N_k = ker(t^k) and I_k = range(t^k), for k in the natural numbers, including zero.
The proof on printed278/PDF284 uses actual quotient spaces
E_k = N_(k+1)/N_k and F_k = I_k/I_(k+1).
Each denominator is a submodule of its numerator via the actual inclusion.
There is no finite-dimensionality or eventual-stability hypothesis on these
constructions or on the exact-sequence assertions below.

Write alpha_k, beta_k and gamma_k for the arrows induced respectively by t,
t^k and t. These names in this note are mathematical notation, not published
Lean declarations.

| Source assertion, printed278/PDF284 | Exact content | Formal status and next owner |
| --- | --- | --- |
| Quotients and arrows | alpha_k : E_(k+1) -> E_k, beta_k : E_k -> F_k, gamma_k : F_k -> F_(k+1), with the indicated representative formulas | Definition task 9b1984a4-2185-4310-bfc4-393380056a9e revision 1, published by Worker 709; no candidate or accepted construction at this audit |
| Kernel of beta_k | (N_k + (range(t) intersect N_(k+1)))/N_k, as the corresponding submodule of E_k | Retained statement and proof successors after the actual maps are public |
| Image of beta_k | (I_(k+1) + t^k(N_(k+1)))/I_(k+1), as a submodule of F_k | Same successors |
| First arrow | alpha_k is injective; its image is (N_k + t(N_(k+2)))/N_k, equal to the displayed kernel of beta_k | Same successors; retain the k+2 index |
| Last arrow | gamma_k is surjective; its kernel equals the displayed image of beta_k | Same successors |
| Five-term sequence | 0 -> E_(k+1) -> E_k -> F_k -> F_(k+1) -> 0 is exact | Same successors; use equality of actual ranges and kernels and the endpoint injectivity/surjectivity |

The first-arrow paragraph initially describes the composite
N_(k+2) -> N_(k+1) -> E_k. Its kernel is N_(k+1); passing to the quotient
gives the injective arrow from E_(k+1). Assigning that nonzero kernel to the
induced quotient arrow would misstate the assertion. The 2010 errata's
correction to the image index N_(k+2) is already incorporated in the 2026 text.
The last repeated I_k in the common-index proof is a prose typo; the current
statement Markdown already records the increasing/decreasing comparison.

The existing namespace
`Langlands.LinearAlgebra.StableEndomorphism` in
`Langlands/LinearAlgebra/StableEndomorphismStatements.lean` defines `Stable`,
`EventuallyStable` and six Prop-valued targets, aggregated in
`StableEndomorphismStatement`. These cover the complementary-kernel/range
criterion, exact-row transfer, monotonicity and the common first stabilization
index for arbitrary-dimensional complex spaces with independent carrier
universes. They expressly exclude the auxiliary quotient assertions above.
Artifact 4fa7a40f-54a4-4ce8-9f84-270267ded0fa was verified as independently
accepted and published at commit 24af03c708d2441a8b505c2999c4fd8905a0559d.
It is statement evidence. Proof task
38e30030-51f9-46f9-8e89-9b9b9a5020b7 owns that aggregate; this audit supplies
no accepted proof of it. An alternate proof of the common-index target does
not discharge the source's additional quotient assertions.

## Actual localization prerequisites

The following distinguishes already public constructions from the missing
interfaces needed by C.II.

| Passage or prerequisite | Current interface or task | Remaining boundary |
| --- | --- | --- |
| A.III.1 example 4, printed252/PDF258 | `Langlands.Renard.ModuleLocalization` in `Langlands/Algebra/RenardModuleLocalization.lean`: actual `LocalizedModule`, `IsSLocal`, inverse action, `factor`, representative, factorization, uniqueness and comparison laws | Full-subcategory and universal-arrow category packaging remain separate |
| First assertion of example 5, printed252/PDF258 | `Langlands.Algebra.PolynomialEndomorphism.equivalence` and `fieldEquivalence`, with actual evaluation actions and linear-intertwiner correspondence | These equivalences do not construct endomorphism localization |
| Localization at powers of X in example 5, printed252–253/PDF258–259 | Definition task 70d44244-d27d-47c1-a8c9-89fece05f06e revision 1, published by Worker 709 | Actual localized carrier, invertible X action, canonical map, fraction formulas and unique factorization into invertible targets; no candidate or accepted construction at this audit |
| Final sentence of example 5 | Retained general algebra-action extension | Preserve noncommutative and possibly nonunital B and its module-action conventions; an ordinary unital `Module B V` does not cover the full assertion |
| Unnumbered lemma and corollary, printed253/PDF259 | Retained statement/proof successors over the actual localization interface | Injective case; K = union_n ker(a^n); induced injective quotient action; compatible quotient-localization identification; inverse-iterate exhaustion and its converse; surjective canonical map gives localization isomorphic to V/K |

The example-4 artifact 9652aa10-f220-4739-a962-777ceedbd047 was verified as
accepted and public at commit 6e568b3024e33889aa9fcaae1e910b0ff99f9b59; the
exact public Lean/Markdown pair was read. The construction retains arbitrary
commutative coefficient rings, arbitrary unital modules, independent source
and target universes, and zero denominators. Its formal counterexample explains
why invertibility of a scalar endomorphism does not imply an inverse coefficient
in the original ring. Preserve Worker 618's example-4 task ownership
08bb9432-0606-45f0-a725-70e8b0dda929 and Worker 490's polynomial-equivalence
work under task 959d6ee1-9a1f-4812-a911-7cf695869dd1.

The current `Langlands/Algebra/NonUnitalModule.lean` and paired Markdown were
read. They provide actual ambient actions and additive intertwiners, with named
adapters for ordinary unital modules. They supply neither a compatibility law
with a separate complex-vector-space structure nor endomorphism localization.
Extending each commuting B-action map by the vector-localization universal
property is a proposed route. It still requires a precise compatible action
interface and proofs of its laws, B-linearity and universal factorization.
This proposal is not a checked implementation or a new assumption permitted
in the final theorem.

## Final finite-localization proposition

The proposition on printed279/PDF285 takes a commutative noetherian complex
algebra B, a finite B-module L and a B-linear endomorphism a. Its actual
localization L_a is also assumed finite over B. It concludes that a is
eventually stable. For every positive n with a^n stable, set K = ker(a^n)
and I = range(a^n): the required conclusions are L = K direct-sum I and an
isomorphism of the localized pair with (I, a restricted to I), intertwining
the actual operators. Finite-dimensionality over the complex numbers is not
a source hypothesis.

This proposition has no dedicated published Lean target or accepted proof in
this audit. The source proof uses finiteness of End_B(L_a), integrality of the
inverse localized operator, invariance of the canonical image under that inverse,
surjectivity of L -> L_a, the kernel-union/quotient description from A.III.1,
and noetherian stabilization. These are proof dependencies to discharge,
not hypotheses to add to the proposition. Its precise B/module conventions
and the final pair identification must be checked against the eventual
published action and localization interfaces before publishing its statement.

The dependency order is actual quotient/localization definitions, then exact
Prop-valued statements over their published names, then independent proof
tasks. General B-action and stability adapters precede the final proposition
where needed. The whole-book parent retains every item not assigned to a
focused task above. Neither this note, the planning DAG nor task publication
closes any of those mathematical obligations.
